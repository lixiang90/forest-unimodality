import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell172.Parameters
import ForestUnimodality.BinomialMassData.Q53_90.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_90.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_90.Batch100_149
import ForestUnimodality.BinomialMassData.Q107_180.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_180.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_180.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree000.table
  base := (364192034872192043931438121/25000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-4368984064357989832716455750000000000000)
      constant := (364192034872192043931438121000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree000.table
  base := (364192034872192043931438121/25000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-8737968128715979665432911500000000000000)
      constant := (728384069744384087862876242000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree001.table
  base := (43668972490284792906511442596679282407407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-163730117555323952567569725285000000000000)
      constant := (5978254133002494003138480548431453124999945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree001.table
  base := (5424072664169686006328590594758521412037/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-328323773748716928287672005665000000000000)
      constant := (11883704270481447264170357312260781249999920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9819984662179065683/20000000000000000000)
  directionHi := (1534372603465479013/3125000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree002.table
  base := (21432342393890119117570326740639/4000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-209497665372982179651795145320000000000000)
      constant := (3809545472978561367447352536151831250000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree002.table
  base := (6617675258944926540994319896460474537037/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-420722408022102405608655400830000000000000)
      constant := (7537429766228439679015875539356812499999960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/20000000000000000000)
  centralHi := (1534372603465479013/3125000000000000000)
  directionLo := (6943777745774705409/10000000000000000000)
  directionHi := (69437777457747054091/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree003.table
  base := (4213669755769099732607359310250848240833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-9454267155208903953185946865000000000000)
      constant := (96483933692666084163027641848266964816660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree003.table
  base := (16571676164236358475177641142204767080273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-57013449143943098103293199555000000000000)
      constant := (571361341824755262335798708798518012408190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6943777745774705409/10000000000000000000)
  centralHi := (69437777457747054091/100000000000000000000)
  directionLo := (85043561822206196959/100000000000000000000)
  directionHi := (531522261388788731/625000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree004.table
  base := (21717484549766762024069409183874738215763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-602065522016597267640491970780000000000000)
      constant := (3918827193309006697386716257775089659128005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree004.table
  base := (4251841889022913911432774281736357563863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-605519676568873360250622191160000000000000)
      constant := (3870377667498577054664369926590041355607525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85043561822206196959/100000000000000000000)
  centralHi := (531522261388788731/625000000000000000)
  directionLo := (9819984662179065683/10000000000000000000)
  directionHi := (98199846621790656831/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree005.table
  base := (2845564836004234672319843212289428695137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-693600617651913721808942810850000000000000)
      constant := (3289224740073524908180018205282864369217475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree005.table
  base := (13866155208505772070202990137860085994717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-697918310842258837571605586325000000000000)
      constant := (3259726080703587019388479766670486609286795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/10000000000000000000)
  centralHi := (98199846621790656831/100000000000000000000)
  directionLo := (109790766213188494833/100000000000000000000)
  directionHi := (54895383106594247417/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree006.table
  base := (9343549684533393444681863767816664482649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-87237301476358908441932627880000000000000)
      constant := (340583708958429665477770030055249967239735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree006.table
  base := (1811143336478416889326914874611318199057/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-29270997967246085736762554870000000000000)
      constant := (113061239616426105533754786891782954976425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109790766213188494833/100000000000000000000)
  centralHi := (54895383106594247417/50000000000000000000)
  directionLo := (30067439630369692087/25000000000000000000)
  directionHi := (120269758521478768349/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree007.table
  base := (1498144730312751820381365683214911289157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-438335404461273315072922245495000000000000)
      constant := (1551091012894478458427273680725776048072390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree007.table
  base := (2878428381302604767147483357077792854629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-882715579389029792213572376655000000000000)
      constant := (3104569825255610429190974615797379070749830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30067439630369692087/25000000000000000000)
  centralHi := (120269758521478768349/100000000000000000000)
  directionLo := (64953093236486084389/50000000000000000000)
  directionHi := (129906186472972168779/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree008.table
  base := (1782867321803214551868336256811892514429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-484102952278931542157147665530000000000000)
      constant := (1658885873638085306055384259173605489447915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree008.table
  base := (1682564143013160914850737992515667793139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-975114213662415269534555771820000000000000)
      constant := (3333874780518862315757102567051230304147530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64953093236486084389/50000000000000000000)
  centralHi := (129906186472972168779/100000000000000000000)
  directionLo := (138875554915494108181/100000000000000000000)
  directionHi := (69437777457747054091/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree009.table
  base := (857065085481612836622294172593847725683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-19624833336910732194124929095000000000000)
      constant := (67868941540770177554241140702219238628415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree009.table
  base := (768278433101829798665392474663055236373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-39537512886511138772427376555000000000000)
      constant := (136819696046750839807930195293755552363730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138875554915494108181/100000000000000000000)
  centralHi := (69437777457747054091/50000000000000000000)
  directionLo := (29459953986537197049/20000000000000000000)
  directionHi := (73649884966342992623/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree010.table
  base := (235669811406182993457877560590663738637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-1151276095828495992651197011200000000000000)
      constant := (4116352395156659954769476690129739604715995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree010.table
  base := (2921133367388863941395970649563662181/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-1159911482209186224176522562150000000000000)
      constant := (4158595450677253839144533497429777359860875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29459953986537197049/20000000000000000000)
  centralHi := (73649884966342992623/50000000000000000000)
  directionLo := (155267590602024943933/100000000000000000000)
  directionHi := (77633795301012471967/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree011.table
  base := (-988603456632819896062057598011577259083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-1242811191463812446819647851270000000000000)
      constant := (4656001205229685382972923097667937070023795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree011.table
  base := (-570759903523728457071634989816712939029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-1252310116482571701497505957315000000000000)
      constant := (4711597315666515567841650236966862506462170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155267590602024943933/100000000000000000000)
  centralHi := (77633795301012471967/50000000000000000000)
  directionLo := (40711505714366107163/25000000000000000000)
  directionHi := (162846022857464428653/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree012.table
  base := (-2030268560936174535201548147714984961331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-49420232855523292629188840420000000000000)
      constant := (195340967339631222764989116045425075193345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree012.table
  base := (-272086217591122019373607842275191206129/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-149412083417328575424276594720000000000000)
      constant := (593749010388131592441885733144977055264520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40711505714366107163/25000000000000000000)
  centralHi := (162846022857464428653/100000000000000000000)
  directionLo := (85043561822206196959/50000000000000000000)
  directionHi := (170087123644412393919/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree013.table
  base := (-733417222609572532922308773540286176887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-712940691367222677578274765705000000000000)
      constant := (2982490388235793803385729630521872732240510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree013.table
  base := (-96110321107077693293488751980463409517/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-1437107385029342656139472747645000000000000)
      constant := (6049215195000762373262879839165773070886560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85043561822206196959/50000000000000000000)
  centralHi := (170087123644412393919/100000000000000000000)
  directionLo := (177032291118782711467/100000000000000000000)
  directionHi := (44258072779695677867/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree014.table
  base := (-465912464277782599579874909073564330397/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-758708239184880904662500185740000000000000)
      constant := (3362239159404050727161404284181275261585620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree014.table
  base := (-241607200384617672901482605163960272581/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-1529506019302728133460456142810000000000000)
      constant := (6824283657862373763954638796341345811225040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177032291118782711467/100000000000000000000)
  centralHi := (44258072779695677867/25000000000000000000)
  directionLo := (45928772686561385629/25000000000000000000)
  directionHi := (183715090746245542517/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree015.table
  base := (-276892478898730195390027485921618945561/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 75000000000000000000000000000000000000000
      center := (159)
      previous := (0)
      next := (111)
      square := (4317693190345115762662775475000000000000)
      linear := (-89386198555837681305191733975000000000000)
      constant := (419450985006512167601286565433155726532680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree015.table
  base := (-2282927814210395940200953392073506920771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-60070542725041244843757019925000000000000)
      constant := (283941999414230333201462243682389930792290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45928772686561385629/25000000000000000000)
  centralHi := (183715090746245542517/100000000000000000000)
  directionLo := (23770398160394867557/12500000000000000000)
  directionHi := (190163185283158940457/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree016.table
  base := (-1264013880415247873615160122102998625693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-850243334820197358830951025810000000000000)
      constant := (4220041847093815826893475882248190371062890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree016.table
  base := (-129727317712334511494049409163931299117/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-1714303287849499088102422933140000000000000)
      constant := (8573892116520365534838574753602770984768200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23770398160394867557/12500000000000000000)
  centralHi := (190163185283158940457/100000000000000000000)
  directionLo := (9819984662179065683/5000000000000000000)
  directionHi := (196399693243581313661/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree017.table
  base := (-21931815628980289271450713983303225831/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-896010882637855585915176445845000000000000)
      constant := (4696518673655357832334149422016270257640320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree017.table
  base := (-2872582563037723247025258410463430984119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-1806701922122884565423406328305000000000000)
      constant := (9545343333110800650563132156081248634287870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/5000000000000000000)
  centralHi := (196399693243581313661/100000000000000000000)
  directionLo := (101222085010274119001/50000000000000000000)
  directionHi := (202444170020548238003/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree018.table
  base := (-6113392066102742277232664421871614625359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-69761365218926949111066804880000000000000)
      constant := (385479506411993811129285174704641926873205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree018.table
  base := (-249664667106182779501673685081444292043/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-70337057644306297879421841610000000000000)
      constant := (391843304497396337427263718503319463494625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101222085010274119001/50000000000000000000)
  centralHi := (202444170020548238003/100000000000000000000)
  directionLo := (6509791636663786321/3125000000000000000)
  directionHi := (208313332373241162273/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree019.table
  base := (-6558719256428366724315480302671238061049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-1975091956546344080167254571830000000000000)
      constant := (11483985209792321935838970073618882861758385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree019.table
  base := (-267380630017588683642624395482672030469/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-1991499190669655520065373118635000000000000)
      constant := (11676350549203856281895535707833356897167125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6509791636663786321/3125000000000000000)
  centralHi := (208313332373241162273/100000000000000000000)
  directionLo := (214021603847789737363/100000000000000000000)
  directionHi := (53505400961947434341/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree020.table
  base := (-6955584480371241837111162783997532295391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-2066627052181660534335705411900000000000000)
      constant := (12620470112685501820992980044960333140122215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree020.table
  base := (-1415778993887864244272751154219951772529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-2083897824943040997386356513800000000000000)
      constant := (12834407912057127855881216765351532553542925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214021603847789737363/100000000000000000000)
  centralHi := (53505400961947434341/25000000000000000000)
  directionLo := (109790766213188494833/50000000000000000000)
  directionHi := (219581532426376989667/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree021.table
  base := (-3654135403391111241308358786848970857271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-39965965700314388676002893555000000000000)
      constant := (255867095694601984239039515935005145713645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree021.table
  base := (-3714514144929343946423645334412351530527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-241810717690714052745259989885000000000000)
      constant := (1561484925115199946727519678004004454084190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109790766213188494833/50000000000000000000)
  centralHi := (219581532426376989667/100000000000000000000)
  directionLo := (112502057594352304197/50000000000000000000)
  directionHi := (45000823037740921679/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree022.table
  base := (-952559288063208290699882381391224297/1250000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-1124848621726146721336303546020000000000000)
      constant := (7536272702483674817420449039497738879620000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree022.table
  base := (-7738611986117549565951352580035008253993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-2268695093489811952028323304130000000000000)
      constant := (15332720794096207393736173087914773885710945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112502057594352304197/50000000000000000000)
  centralHi := (45000823037740921679/20000000000000000000)
  directionLo := (115149527051772616389/50000000000000000000)
  directionHi := (230299054103545232779/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree023.table
  base := (-7895431116514494875137915227119633201929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-2341232339087609896841057932110000000000000)
      constant := (16387199945760684875065509419014349517739585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree023.table
  base := (-4005443764597258675270850167604433174913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-2361093727763197429349306699295000000000000)
      constant := (16672039717653238975614827280873178042773490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115149527051772616389/50000000000000000000)
  centralHi := (230299054103545232779/100000000000000000000)
  directionLo := (58868740001657212719/25000000000000000000)
  directionHi := (235474960006628850877/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree024.table
  base := (-8136006680545803798260720679698116112207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-270307492746991816778834308020000000000000)
      constant := (1973377772866000550503696023612528258316895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree024.table
  base := (-2062182084472443474014201603627246216781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-90870087482836403950751484980000000000000)
      constant := (669293821672958133648497996151455075664380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58868740001657212719/25000000000000000000)
  centralHi := (235474960006628850877/100000000000000000000)
  directionLo := (240539517042957536697/100000000000000000000)
  directionHi := (120269758521478768349/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree025.table
  base := (-2086190180009062216047405588902990229101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-1262151265179121402588979806125000000000000)
      constant := (9595899936201680672199586310839942638142730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree025.table
  base := (-8454703333260809751782303065677154532961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-2545890996309968383991273489625000000000000)
      constant := (19529054392303338068266468580117959138050265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240539517042957536697/100000000000000000000)
  centralHi := (120269758521478768349/50000000000000000000)
  directionLo := (9819984662179065683/4000000000000000000)
  directionHi := (61374904138619160519/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree026.table
  base := (-4261998094946182501451484864952484897993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-1307918812996779629673205226160000000000000)
      constant := (10340544398338185914558078733692414538770945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree026.table
  base := (-8631125058720379454952755990922278469403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-2638289630583353861312256884790000000000000)
      constant := (21046091145692922492359228963160992406630595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/4000000000000000000)
  centralHi := (61374904138619160519/25000000000000000000)
  directionLo := (250361467078164534783/100000000000000000000)
  directionHi := (488987240387040107/195312500000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree027.table
  base := (-1084474651455532133977982407894239143849/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-50136531882016216916941875785000000000000)
      constant := (411629358744564300980224087545365217123020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree027.table
  base := (-4390043573601493526564409174772233745967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-101136602402101456986416306665000000000000)
      constant := (837842992773794993865445884026402662540330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250361467078164534783/100000000000000000000)
  centralHi := (488987240387040107/195312500000000000)
  directionLo := (127565342733309295439/50000000000000000000)
  directionHi := (255130685466618590879/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree028.table
  base := (-440102959173892130770401509427144491577/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-1399453908632096083841656066230000000000000)
      constant := (11916116860119281873672738802697354936371050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree028.table
  base := (-8903494170865824695641172406078643807427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-2823086899130124815954223675120000000000000)
      constant := (24255806252660744154130256191061383085997355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127565342733309295439/50000000000000000000)
  centralHi := (255130685466618590879/100000000000000000000)
  directionLo := (64953093236486084389/25000000000000000000)
  directionHi := (259812372945944337557/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree029.table
  base := (-278266035812967959758412731955365189017/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-1445221456449754310925881486265000000000000)
      constant := (12746800075144348073371717618746161191723280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree029.table
  base := (-9003085866273879559347195106590935126767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-2915485533403510293275207070285000000000000)
      constant := (25947992624561487182773135042487598757886455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64953093236486084389/25000000000000000000)
  centralHi := (259812372945944337557/100000000000000000000)
  directionLo := (13220558952341828993/5000000000000000000)
  directionHi := (264411179046836579861/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree030.table
  base := (-1796949162019512832697421962745863458653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-110443629945734262074822733800000000000000)
      constant := (1007847053940489314554822651081353413533675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree030.table
  base := (-9080457090355523056099622276971259645663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-334209351964099530066243385050000000000000)
      constant := (3077567179434373753299506231832931105315055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13220558952341828993/5000000000000000000)
  centralHi := (264411179046836579861/100000000000000000000)
  directionLo := (8404104865359722709/3125000000000000000)
  directionHi := (268931355691511126689/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree031.table
  base := (-4522108114878028662620337035246110758241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-1536756552085070765094332326335000000000000)
      constant := (14493423833128999763985825087431525047637465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree031.table
  base := (-4568537230529219437474720124424760896267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-3100282801950281247917173860615000000000000)
      constant := (29505944230281436646875636168317689558007910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8404104865359722709/3125000000000000000)
  centralHi := (268931355691511126689/100000000000000000000)
  directionLo := (34172100403511258573/12500000000000000000)
  directionHi := (54675360645618013717/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree032.table
  base := (-9084269830036622229225036461063881356301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-3165048199805457984357115492740000000000000)
      constant := (30818350147501827567438907628284376016899365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree032.table
  base := (-183485807514858241568973344704598188727/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-3192681436223666725238157255780000000000000)
      constant := (31371328897034067300868852829195962226092750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34172100403511258573/12500000000000000000)
  centralHi := (54675360645618013717/20000000000000000000)
  directionLo := (277751109830988216363/100000000000000000000)
  directionHi := (69437777457747054091/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree033.table
  base := (-9106150316653564301438545420548663908037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-361842588382308270947285148090000000000000)
      constant := (3634023333317029375430245211191270041379445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree033.table
  base := (-9193354924875092238860080177227967189947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-121669632240631563057745950035000000000000)
      constant := (1233114438998308353682212266002985164050265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277751109830988216363/100000000000000000000)
  centralHi := (69437777457747054091/25000000000000000000)
  directionLo := (141028792699825557183/50000000000000000000)
  directionHi := (282057585399651114367/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree034.table
  base := (-9111009868248580406114981818864322893277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-3348118391076090892694017172880000000000000)
      constant := (34650271679195680885599987574735316409407605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree034.table
  base := (-2298856524122851023706903299214612846543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-3377478704770437679880124046110000000000000)
      constant := (35274070769657294052811340120499609062866780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141028792699825557183/50000000000000000000)
  centralHi := (282057585399651114367/100000000000000000000)
  directionLo := (17893705679151503397/6250000000000000000)
  directionHi := (286299290866424054353/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree035.table
  base := (-9099917922077521525641175072118732574387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-3439653486711407346862468012950000000000000)
      constant := (36650390811499537205000027679151471102457755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree035.table
  base := (-2295394644807166356673363548716568825739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-3469877339043823157201107441275000000000000)
      constant := (37311126564177002410697484277852427834100940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17893705679151503397/6250000000000000000)
  centralHi := (286299290866424054353/100000000000000000000)
  directionLo := (72619765912832354029/25000000000000000000)
  directionHi := (290479063651329416117/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree036.table
  base := (-362954751917984913735327502731336455899/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-130784762309137918556700698260000000000000)
      constant := (1433571598651503206937700325614582943012625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree036.table
  base := (-9152811406975582646005331449460325348717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-131936147159896616093410771720000000000000)
      constant := (1459448976553276861389600753206698373256415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72619765912832354029/25000000000000000000)
  centralHi := (290479063651329416117/100000000000000000000)
  directionLo := (29459953986537197049/10000000000000000000)
  directionHi := (294599539865371970491/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree037.table
  base := (-4516894177815804128993781109500717558349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-1811361838991020127599684846545000000000000)
      constant := (20409136872200160653118173809495153129622885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree037.table
  base := (-4555027319635808102339865608284128587481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-3654674607590594111843074231605000000000000)
      constant := (41555932619903885432267822652134660281380130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29459953986537197049/10000000000000000000)
  centralHi := (294599539865371970491/100000000000000000000)
  directionLo := (149331586878015104147/50000000000000000000)
  directionHi := (59732634751206041659/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree038.table
  base := (-8980539842877541150253273273760444403511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-3714258773617356709367820533160000000000000)
      constant := (42985796015481942805347482637660340005526015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree038.table
  base := (-9054175233896238004021683176041811284351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-3747073241863979589164057626770000000000000)
      constant := (43763440283773004228267112217733855476612615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149331586878015104147/50000000000000000000)
  centralHi := (59732634751206041659/20000000000000000000)
  directionLo := (60534450960477206207/20000000000000000000)
  directionHi := (75668063700596507759/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree039.table
  base := (-8914929061591740245212535234517193209153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-140955328490839746797639680490000000000000)
      constant := (1674403377539939557658220921845914033954235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree039.table
  base := (-8985982238638605840521010377444549749241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-426607986237485007387226780215000000000000)
      constant := (5114170681899366149221218102409706753761385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60534450960477206207/20000000000000000000)
  centralHi := (75668063700596507759/25000000000000000000)
  directionLo := (306628922798056178893/100000000000000000000)
  directionHi := (153314461399028089447/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree040.table
  base := (-2209427239058439393953288854744718648319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-1948664482443994808852361106650000000000000)
      constant := (23743728815593778768030920193818925964953870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree040.table
  base := (-4453115702976374619545242219823844055119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-3931870510410750543806024417100000000000000)
      constant := (48348118153286464790576150595447562105117870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306628922798056178893/100000000000000000000)
  centralHi := (153314461399028089447/50000000000000000000)
  directionLo := (310535181204049887867/100000000000000000000)
  directionHi := (77633795301012471967/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree041.table
  base := (-218739592748325719871719202584904903833/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-1994432030261653035936586526685000000000000)
      constant := (24910700131793518715043634251880506759650900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree041.table
  base := (-8815629315631767818398324679280481170771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-4024269144684136021127007812265000000000000)
      constant := (50725090944077444122502465631269510041945915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310535181204049887867/100000000000000000000)
  centralHi := (77633795301012471967/25000000000000000000)
  directionLo := (39299113626011000107/12500000000000000000)
  directionHi := (314392909008088000857/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree042.table
  base := (-1730242483763501238966001829309608211193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-453377684017624725115735988160000000000000)
      constant := (5801181123644392686596379266363779384160525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree042.table
  base := (-2178709268930032707478166414263002702247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-152469176998426722164740415090000000000000)
      constant := (1968828342958564073697100365313239945955060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39299113626011000107/12500000000000000000)
  centralHi := (314392909008088000857/100000000000000000000)
  directionLo := (318203871289624167739/100000000000000000000)
  directionHi := (15910193564481208387/5000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree043.table
  base := (-8543212402978311344075272887745342769831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-4171934251793938980210074733510000000000000)
      constant := (54655063840612746372171191832369878726072815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree043.table
  base := (-2151118414960031283238175639776733429161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-4209066413230906975768974602595000000000000)
      constant := (55647857539258813666525791941881938948253060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318203871289624167739/100000000000000000000)
  centralHi := (15910193564481208387/5000000000000000000)
  directionLo := (6439394573182777287/2000000000000000000)
  directionHi := (321969728659138864351/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree044.table
  base := (-4213081101344755279710223493307749859253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-2131734673714627717189262786790000000000000)
      constant := (28577311672044837527864229487499453769000845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree044.table
  base := (-4242559464670152044430907024645678577429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-4301465047504292453089957997760000000000000)
      constant := (58193489500928140448833355746923666784094170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6439394573182777287/2000000000000000000)
  centralHi := (321969728659138864351/100000000000000000000)
  directionLo := (65138409142985771461/20000000000000000000)
  directionHi := (162846022857464428653/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree045.table
  base := (-4150302150258182744627424094575274430941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-80648230427121701639758822475000000000000)
      constant := (1105726581260814998287160316008373627845295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree045.table
  base := (-835731638072034124454550685160710617309/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-162735691917691775200405236775000000000000)
      constant := (2251673621217102015107857698920089469134550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65138409142985771461/20000000000000000000)
  centralHi := (162846022857464428653/50000000000000000000)
  directionLo := (329372298639565484499/100000000000000000000)
  directionHi := (658744597279130969/200000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree046.table
  base := (-816704760341698818374021168235273985879/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-2223269769349944171357713626860000000000000)
      constant := (31159415635078202900366975925242190059531675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree046.table
  base := (-8221575652288711480518171145168042737999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-4486262316051063407731924788090000000000000)
      constant := (63452883553888011434892755639457814230370135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329372298639565484499/100000000000000000000)
  centralHi := (658744597279130969/200000000000000000)
  directionLo := (66602376408127334501/20000000000000000000)
  directionHi := (166505941020318336253/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree047.table
  base := (-2006492428397019101653310124466101320829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-2269037317167602398441939046895000000000000)
      constant := (32491673257005154268652944211911902643376170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree047.table
  base := (-8078374818683902025005697061164681460599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-4578660950324448885052908183255000000000000)
      constant := (66166512303930715753964653885059143002819135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66602376408127334501/20000000000000000000)
  centralHi := (166505941020318336253/50000000000000000000)
  directionLo := (67322423025135604829/20000000000000000000)
  directionHi := (168306057562839012073/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree048.table
  base := (-3938909506200356231166535486733276737781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-85733513517972615760228313590000000000000)
      constant := (1253754084965937444557786729238333616311095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree048.table
  base := (-7928162497511547233794001611442196507329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-519006620510870484708210175380000000000000)
      constant := (7659557051068122969677417090116367052390065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67322423025135604829/20000000000000000000)
  centralHi := (168306057562839012073/50000000000000000000)
  directionLo := (340174247288824787837/100000000000000000000)
  directionHi := (170087123644412393919/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree049.table
  base := (-7723016578137812916593851550630728124377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-4721144825605837705220779773930000000000000)
      constant := (70476896647039152470809026676024351703209105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree049.table
  base := (-3885679894369742234660476772287606452299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-4763458218871219839694874973585000000000000)
      constant := (71761330172439526310359943136364721257879270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340174247288824787837/100000000000000000000)
  centralHi := (170087123644412393919/50000000000000000000)
  directionLo := (68739892635253459781/20000000000000000000)
  directionHi := (171849731588133649453/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree050.table
  base := (-94524474440462007660676758970551579181/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-2406339960620577079694615307000000000000000)
      constant := (36652910646073413123752306459684021472422600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree050.table
  base := (-1902090516126583835190331470435761847939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-4855856853144605317015858368750000000000000)
      constant := (74642409067171260586515627503152188602112940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68739892635253459781/20000000000000000000)
  centralHi := (171849731588133649453/50000000000000000000)
  directionLo := (173594443644367635227/50000000000000000000)
  directionHi := (69437777457747054091/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree051.table
  base := (-1479002958049064244318236432498889615689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-544912779652941179284186828230000000000000)
      constant := (8465493816799975107854757134558083278823325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree051.table
  base := (-929942578065132889872361574622390640933/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-183268721756221881271734880145000000000000)
      constant := (2873303704383244426444340645367229374362680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173594443644367635227/50000000000000000000)
  centralHi := (69437777457747054091/20000000000000000000)
  directionLo := (175321794085850836873/50000000000000000000)
  directionHi := (350643588171701673747/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree052.table
  base := (-7222536347613724157961831003533948218821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-4995750112511787067726132294140000000000000)
      constant := (79127718673497139669327455110010916990459165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree052.table
  base := (-1453048846033532754357902320785090730467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-5040654121691376271657825159080000000000000)
      constant := (80571655943181703637149512083312063756934775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175321794085850836873/50000000000000000000)
  centralHi := (350643588171701673747/100000000000000000000)
  directionLo := (70812916447513084587/20000000000000000000)
  directionHi := (44258072779695677867/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree053.table
  base := (-7044850916719162709719755504334616026239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-5087285208147103521894583134210000000000000)
      constant := (82120599939973023249561790400750326836457735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree053.table
  base := (-1417160105741043473659100680973161030917/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-5133052755964761748978808554245000000000000)
      constant := (83619732609293597146643758210534491304131025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70812916447513084587/20000000000000000000)
  centralHi := (44258072779695677867/12500000000000000000)
  directionLo := (89363209314641031859/25000000000000000000)
  directionHi := (357452837258564127437/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree054.table
  base := (-6862267120047616366413337842535804843483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-191808159399348888002334591640000000000000)
      constant := (3154372092095993314085436610713320975782585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree054.table
  base := (-3450758688753898174394518624079638293189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-193535236675486934307399701830000000000000)
      constant := (3211977350219917787520018257705703617068110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89363209314641031859/25000000000000000000)
  centralHi := (357452837258564127437/100000000000000000000)
  directionLo := (180404637782218152523/50000000000000000000)
  directionHi := (360809275564436305047/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree055.table
  base := (-3337537565621194088255971457097230320879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-2635177699708868215115742407175000000000000)
      constant := (44135009569955841225009542557285623906681335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree055.table
  base := (-839085509633944861762497363428631040467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-5317850024511532703620775344575000000000000)
      constant := (89882584427547271631927684446431453476295640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180404637782218152523/50000000000000000000)
  centralHi := (360809275564436305047/100000000000000000000)
  directionLo := (91033694243693752163/25000000000000000000)
  directionHi := (364134776974775008653/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree056.table
  base := (-6483547810686519538479042834906593083483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-5361890495053052884399935654420000000000000)
      constant := (91426481063780901569906111541079609933729795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree056.table
  base := (-3259786260243697921626083098589156824843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-5410248658784918180941758739740000000000000)
      constant := (93097283818554800990037114570708927657292390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91033694243693752163/25000000000000000000)
  centralHi := (364134776974775008653/100000000000000000000)
  directionLo := (45928772686561385629/12500000000000000000)
  directionHi := (367430181492491085033/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree057.table
  base := (-6287941765408224156280573525962422730651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-201978725581050716243273573870000000000000)
      constant := (3505088800601876592219720978496687886346745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree057.table
  base := (-395152391637743146973022935239198061743/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-611405254784255962029193570545000000000000)
      constant := (10707494680952201067933356630179967465181680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45928772686561385629/12500000000000000000)
  centralHi := (367430181492491085033/100000000000000000000)
  directionLo := (370696291781750550519/100000000000000000000)
  directionHi := (9267407294543763763/2500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree058.table
  base := (-6088498339348668065935728040338018747103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-5544960686323685792736837334560000000000000)
      constant := (97902736215888924295235558687412367469141095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree058.table
  base := (-6121521540160294048978438533886763676171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-5595045927331689135583725530070000000000000)
      constant := (99693056927090498525976439010084786903716915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370696291781750550519/100000000000000000000)
  centralHi := (9267407294543763763/2500000000000000000)
  directionLo := (373933875451097026187/100000000000000000000)
  directionHi := (93483468862774256547/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree059.table
  base := (-1471361134847432292794508748966624309007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-2818247890979501123452644087315000000000000)
      constant := (50611233108383308484405680990838761436568110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree059.table
  base := (-5917048172730833957812592340117815663957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-5687444561605074612904708925235000000000000)
      constant := (103074067727016347085751224042681469885365805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373933875451097026187/100000000000000000000)
  centralHi := (93483468862774256547/25000000000000000000)
  directionLo := (75428733432031681087/20000000000000000000)
  directionHi := (94285916790039601359/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree060.table
  base := (-5678993901987508296478357628290675853379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-636447875288257633452637668300000000000000)
      constant := (11621839865718019155484034418375639862199315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree060.table
  base := (-5709230475372033996498916321295181462997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-214068266514017040378729345200000000000000)
      constant := (3944831698751878687471732329543524092685015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75428733432031681087/20000000000000000000)
  centralHi := (94285916790039601359/25000000000000000000)
  directionLo := (23770398160394867557/6250000000000000000)
  directionHi := (380326370566317880913/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree061.table
  base := (-546934730478049397781916285291284410379/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-2909782986614817577621094927385000000000000)
      constant := (54012493410747197317256384502478133022994175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree061.table
  base := (-5498268061389189497270247087742338649957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-5872241830151845567546675715565000000000000)
      constant := (110002194397147416084081652632672159282255805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23770398160394867557/6250000000000000000)
  centralHi := (380326370566317880913/100000000000000000000)
  directionLo := (191741330062980911967/50000000000000000000)
  directionHi := (76696532025192364787/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree062.table
  base := (-1051338745425442012718505071032034529547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-5911101068864951609410640694840000000000000)
      constant := (111507724794649882954747809617871376692555775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree062.table
  base := (-1321087153706156831012204441365188186059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-5964640464425231044867659110730000000000000)
      constant := (113549257982210707526156361775662298379528140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191741330062980911967/50000000000000000000)
  centralHi := (76696532025192364787/20000000000000000000)
  directionLo := (38661318276336588609/10000000000000000000)
  directionHi := (386613182763365886091/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree063.table
  base := (-2520605481583430150988073374551601093411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-111159928972227186362575769165000000000000)
      constant := (2130458309420737867667730405300491994532945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree063.table
  base := (-316728038194313266790151359188604459027/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-224334781433282093414394166885000000000000)
      constant := (4338948992492868857076549934024036643277840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38661318276336588609/10000000000000000000)
  centralHi := (386613182763365886091/100000000000000000000)
  directionLo := (194859279709458253167/50000000000000000000)
  directionHi := (77943711883783301267/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree064.table
  base := (-192922651627185972574180257335968186237/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-6094171260135584517747542374980000000000000)
      constant := (118636035981203952708554761091203107371450125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree064.table
  base := (-484833399279956094372463262125470263231/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-6149437732972001999509625901060000000000000)
      constant := (120809266440192446686102179527138615144638150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194859279709458253167/50000000000000000000)
  centralHi := (77943711883783301267/20000000000000000000)
  directionLo := (9819984662179065683/2500000000000000000)
  directionHi := (392799386487162627321/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree065.table
  base := (-230120854937213251209717667912674950947/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-3092853177885450485957996607525000000000000)
      constant := (61140782682288291824285878062261638816221550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree065.table
  base := (-1156640200862214807581916045803601043881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-6241836367245387476830609296225000000000000)
      constant := (124522167844986071067323006838800430436304260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/2500000000000000000)
  centralHi := (392799386487162627321/100000000000000000000)
  directionLo := (395856237154130439367/100000000000000000000)
  directionHi := (49482029644266304921/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree066.table
  base := (-875882295388558193025633111948575759361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-232490424126156200966090520560000000000000)
      constant := (4665974698768302088780297868567285606015975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree066.table
  base := (-880495156479894661824632552316150494593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-703803889057641439350176965710000000000000)
      constant := (14254478577986342872259850877695788712905525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395856237154130439367/100000000000000000000)
  centralHi := (49482029644266304921/12500000000000000000)
  directionLo := (79777932528478816919/20000000000000000000)
  directionHi := (99722415660598521149/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree067.table
  base := (-2077094384321689634989987324675624372031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-3184388273520766940126447447595000000000000)
      constant := (64867635838175985208056187902016540709775815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree067.table
  base := (-2088108461539036852953115817052074541437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-6426633635792158431472576086555000000000000)
      constant := (132113665881752890514166793766027314873812010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79777932528478816919/20000000000000000000)
  centralHi := (99722415660598521149/25000000000000000000)
  directionLo := (8038003867431235951/2000000000000000000)
  directionHi := (401900193371561797551/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree068.table
  base := (-19634400453472243274241048251099188837/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-3230155821338425167210672867630000000000000)
      constant := (66771706046312744589515734132274160950700500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree068.table
  base := (-394791399716451235236932537264559957863/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-6519032270065543908793559481720000000000000)
      constant := (135992226365436705048028933071894844056884950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8038003867431235951/2000000000000000000)
  centralHi := (401900193371561797551/100000000000000000000)
  directionLo := (80977668008219295201/20000000000000000000)
  directionHi := (202444170020548238003/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree069.table
  base := (-739521764337543585327939410371337643773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-727982970923574087621088508370000000000000)
      constant := (15267302384383870071876988695197649676717025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree069.table
  base := (-29741512374663996370330920041148213207/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-244867811271812199485723810255000000000000)
      constant := (5182443413971667076360182276966407366745625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80977668008219295201/20000000000000000000)
  centralHi := (202444170020548238003/50000000000000000000)
  directionLo := (101963648660432646113/25000000000000000000)
  directionHi := (407854594641730584453/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree070.table
  base := (-693298212157664031174804815848663638719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-6643381833947483242758247415400000000000000)
      constant := (141322184103452701855176521505352152043864675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree070.table
  base := (-348565684710154131843391312391528688519/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-6703829538612314863435526272050000000000000)
      constant := (143914887822520377741101948034658936270499350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101963648660432646113/25000000000000000000)
  centralHi := (407854594641730584453/100000000000000000000)
  directionLo := (410799431401147600029/100000000000000000000)
  directionHi := (41079943140114760003/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree071.table
  base := (-3233636058986281286328344154723331332343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-6734916929582799696926698255470000000000000)
      constant := (145292785275735449301472422298251850270133695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree071.table
  base := (-3251925340179870702827265892896946662691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-6796228172885700340756509667215000000000000)
      constant := (147958958729094491126565922759461287200536715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410799431401147600029/100000000000000000000)
  centralHi := (41079943140114760003/10000000000000000000)
  directionLo := (41372330766907727519/10000000000000000000)
  directionHi := (413723307669077275191/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree072.table
  base := (-187446664030804256350492497182761108343/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-126415778244779928723984242510000000000000)
      constant := (2765139094392491703148035103224689555666280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree072.table
  base := (-3016596043573347579805741136239644191589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-255134326191077252521388631940000000000000)
      constant := (5631784118225708430898952323934801779042055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41372330766907727519/10000000000000000000)
  centralHi := (413723307669077275191/100000000000000000000)
  directionLo := (83325332949296464909/20000000000000000000)
  directionHi := (208313332373241162273/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree073.table
  base := (-2763119503886092471134437532416940783511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-6917987120853432605263599935610000000000000)
      constant := (153396348507041978258368997515899212994226015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree073.table
  base := (-347470554197389250061574800030150673653/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-6981025441432471295398476457545000000000000)
      constant := (156212512322219173087317677956243812272454760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83325332949296464909/20000000000000000000)
  centralHi := (208313332373241162273/50000000000000000000)
  directionLo := (52438741082886655159/12500000000000000000)
  directionHi := (419509928663093241273/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree074.table
  base := (-315705717562578520250072883403046834859/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-3504761108244374529716025387840000000000000)
      constant := (78764642607213773604020115844623354709176140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree074.table
  base := (-2541520305699821326609675668993795903009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-7073424075705856772719459852710000000000000)
      constant := (160421969997076769551871370261621337553093785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52438741082886655159/12500000000000000000)
  centralHi := (419509928663093241273/100000000000000000000)
  directionLo := (10559337772679253781/2500000000000000000)
  directionHi := (422373510907170151241/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree075.table
  base := (-2286811011457385539236928219150146289339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-263002122671261685688907467250000000000000)
      constant := (5989492950108886515545498722966749268553305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree075.table
  base := (-575487028349584962817431399744209935379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-796202523331026916671160360875000000000000)
      constant := (18298503646161047726484729783749722403877260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10559337772679253781/2500000000000000000)
  centralHi := (422373510907170151241/100000000000000000000)
  directionLo := (106304452277757746199/25000000000000000000)
  directionHi := (425217809111030984797/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree076.table
  base := (-2046695944636001511908522394716121404807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-7192592407759381967768952455820000000000000)
      constant := (165957410937815393410709917338585323610351055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree076.table
  base := (-206112728652303598735552682722064416039/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-7258221344252627727361426643040000000000000)
      constant := (169006190054307623581052096216623213038347350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106304452277757746199/25000000000000000000)
  centralHi := (425217809111030984797/100000000000000000000)
  directionLo := (214021603847789737363/50000000000000000000)
  directionHi := (428043207695579474727/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree077.table
  base := (-1805376416808682865801244636729243244517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-7284127503394698421937403295890000000000000)
      constant := (170252578825689671764903493473917052161990205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree077.table
  base := (-227391566330826404660315669514407657041/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-7350619978526013204682410038205000000000000)
      constant := (173380931628399036977113869539925814730395720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214021603847789737363/50000000000000000000)
  centralHi := (428043207695579474727/100000000000000000000)
  directionLo := (430850078476790799021/100000000000000000000)
  directionHi := (215425039238395399511/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree078.table
  base := (-1562923834075455298840819011192392891157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-819518066558890541789539348440000000000000)
      constant := (19400200408526585279232135686354114106632645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree078.table
  base := (-98502131780088250339663625880438031633/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-275667356029607358592718275310000000000000)
      constant := (6585583261194722331924298590808064957469360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430850078476790799021/100000000000000000000)
  centralHi := (215425039238395399511/50000000000000000000)
  directionLo := (86727756247372753669/20000000000000000000)
  directionHi := (216819390618431884173/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree079.table
  base := (-329851348917070548476660844000501423219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-3733598847332665665137152488015000000000000)
      constant := (89502538209533932799289190868789614615730870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree079.table
  base := (-1331898104459908332137686123279815050799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-7535417247072784159324376828535000000000000)
      constant := (182295630404484638080134679473809599968142135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86727756247372753669/20000000000000000000)
  centralHi := (216819390618431884173/50000000000000000000)
  directionLo := (436409664262523401627/100000000000000000000)
  directionHi := (109102416065630850407/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree080.table
  base := (-268721085531043522591941271828274670069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-3779366395150323892221377908050000000000000)
      constant := (91731194257601484799278076881006365839081370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree080.table
  base := (-1086786673500153073240472366050489940031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-7627815881346169636645360223700000000000000)
      constant := (186835570294166505196110141843783183858095815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (436409664262523401627/100000000000000000000)
  centralHi := (109102416065630850407/25000000000000000000)
  directionLo := (109790766213188494833/25000000000000000000)
  directionHi := (439163064852753979333/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree081.table
  base := (-829420188764829915843773363298304175517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-283343255034665342170785431710000000000000)
      constant := (6961990071502820376214588618742008479122415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree081.table
  base := (-84075827491199008705988037368655806823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-285933870948872411628383096995000000000000)
      constant := (7090020734418380569963321002648692209658850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109790766213188494833/25000000000000000000)
  centralHi := (439163064852753979333/100000000000000000000)
  directionLo := (88379861959611591147/20000000000000000000)
  directionHi := (55237413724757244467/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree082.table
  base := (-583068945362111646173346247866249027753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-7741802981571280692779657496240000000000000)
      constant := (192539099103868205909553377033716056381253345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree082.table
  base := (-593867892340158026685237444739959029237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-7812613149892940591287327014030000000000000)
      constant := (196080591587081908940666195971699605531053005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88379861959611591147/20000000000000000000)
  centralHi := (55237413724757244467/12500000000000000000)
  directionLo := (444618715833168456229/100000000000000000000)
  directionHi := (44461871583316845623/10000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree083.table
  base := (-8397083070359570339083503930619892489/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-3916669038603298573474054168155000000000000)
      constant := (98579241459553928888493340564435076290279700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree083.table
  base := (-346167240584862183072375177542582345813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-7905011784166326068608310409195000000000000)
      constant := (200785658586025378136800691278563126383315245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444618715833168456229/100000000000000000000)
  centralHi := (44461871583316845623/10000000000000000000)
  directionLo := (55915198758123840073/12500000000000000000)
  directionHi := (89464318012998144117/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree084.table
  base := (-43956463804054301677770926546575257817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-146756910608183585205862206970000000000000)
      constant := (3737627345915174684445790069975267123710915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree084.table
  base := (-24426240022132342687523563789540372489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-888601157604412393992143756040000000000000)
      constant := (22838417139962995039716862766654627577650660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55915198758123840073/12500000000000000000)
  centralHi := (89464318012998144117/20000000000000000000)
  directionLo := (112502057594352304197/25000000000000000000)
  directionHi := (450008230377409216789/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree085.table
  base := (40198888802042970540934182278333752819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-4008204134238615027642505008225000000000000)
      constant := (103279637041160689340001336435908900113261130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree085.table
  base := (75736600085487520409372506761247764989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-8089809052713097023250277199525000000000000)
      constant := (210360872431894628777741930693984911896547030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112502057594352304197/25000000000000000000)
  centralHi := (450008230377409216789/100000000000000000000)
  directionLo := (56584865726808857157/12500000000000000000)
  directionHi := (452678925814470857257/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree086.table
  base := (410198189854593999933823875259749829577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-8107943364112546509453460856520000000000000)
      constant := (211340669196483413209963517726922066226992895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree086.table
  base := (200662105342833704434004532000274369507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-8182207686986482500571260594690000000000000)
      constant := (215231007293724820605897760629635574079766890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56584865726808857157/12500000000000000000)
  centralHi := (452678925814470857257/100000000000000000000)
  directionLo := (7114593077239680763/1562500000000000000)
  directionHi := (455333956943339568833/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree087.table
  base := (132050725562776757397432423496749981641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-911053162194206995957990188510000000000000)
      constant := (24019561826650633840550508676201756248623075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree087.table
  base := (651807599668661692619868644071260960849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-306466900787402517699712740365000000000000)
      constant := (8153931606720974119496823991029481304804245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7114593077239680763/1562500000000000000)
  centralHi := (455333956943339568833/100000000000000000000)
  directionLo := (457973596198312304859/100000000000000000000)
  directionHi := (22898679809915615243/5000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree088.table
  base := (910922955385606127036718495815014504481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-8291013555383179417790362536660000000000000)
      constant := (221065430559088694004277104498903026958104935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree088.table
  base := (45144265046914638983370549842304449047/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-8367004955533253455213227385020000000000000)
      constant := (225136305556184545849116458856286222012426900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457973596198312304859/100000000000000000000)
  centralHi := (22898679809915615243/5000000000000000000)
  directionLo := (460598108207090465557/100000000000000000000)
  directionHi := (230299054103545232779/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree089.table
  base := (581084775117089803688522134855137781507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-4191274325509247935979406688365000000000000)
      constant := (113004393305083539018607930693105193600503445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree089.table
  base := (144315188857412730325413137734672546781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-8459403589806638932534210780185000000000000)
      constant := (230171458984388794532304404237345821350523480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460598108207090465557/100000000000000000000)
  centralHi := (230299054103545232779/50000000000000000000)
  directionLo := (463207750100412741089/100000000000000000000)
  directionHi := (46320775010041274109/10000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree090.table
  base := (1413958946398090793457540104954772618357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-313854953579770826893602378400000000000000)
      constant := (8555782220006890827781722882874773863091785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree090.table
  base := (70334127690002348844341881193773687581/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-316733415706667570735377562050000000000000)
      constant := (8713392930365510208106114355581877368758100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463207750100412741089/100000000000000000000)
  centralHi := (46320775010041274109/10000000000000000000)
  directionLo := (2329013859030374159/500000000000000000)
  directionHi := (465802771806074831801/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree091.table
  base := (833129353629812042945389191402810078537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-4282809421144564390147857528435000000000000)
      constant := (118028713085101112668515885562299129360602495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree091.table
  base := (1659336755597338343216089484780328499109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-8644200858353409887176177570515000000000000)
      constant := (240406751686612458480492749870842719347379715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2329013859030374159/500000000000000000)
  centralHi := (465802771806074831801/100000000000000000000)
  directionLo := (468383416328287635811/100000000000000000000)
  directionHi := (117095854082071908953/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree092.table
  base := (1919038306004336703509948944600860217079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-8657153937924445234464165896940000000000000)
      constant := (241162701179095647222534101875729116129305665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree092.table
  base := (1912454324551108013753780090958862729919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-8736599492626795364497160965680000000000000)
      constant := (245606882662740333946929358167601446468539065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468383416328287635811/100000000000000000000)
  centralHi := (117095854082071908953/25000000000000000000)
  directionLo := (470949920013257701753/100000000000000000000)
  directionHi := (235474960006628850877/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree093.table
  base := (1086134506563792043123950629008483865477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-162012759880736327567270680315000000000000)
      constant := (4561517427562651685018600829058292419327385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree093.table
  base := (1083003619749923148999487768465424105649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-980999791877797871313127151205000000000000)
      constant := (27873555362821733134439698490416337723169470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470949920013257701753/100000000000000000000)
  centralHi := (235474960006628850877/50000000000000000000)
  directionLo := (473502512801811464293/100000000000000000000)
  directionHi := (236751256400905732147/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree094.table
  base := (303240473821470105963708769971205659879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-4420112064597539071400533788540000000000000)
      constant := (125767571123963539957639739753905451056334660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree094.table
  base := (2419969144554693307858998859399723661137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-8921396761173566319139127756010000000000000)
      constant := (256172094936533255184684023219234462694253495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473502512801811464293/100000000000000000000)
  centralHi := (236751256400905732147/50000000000000000000)
  directionLo := (29752588654364219357/6250000000000000000)
  directionHi := (476041418469827509713/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree095.table
  base := (66999429802566961969860046329154191599/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-4465879612415197298484759208575000000000000)
      constant := (128401150611242849273315295414582466317317300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree095.table
  base := (2674315250095382061322110649812819974789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-9013795395446951796460111151175000000000000)
      constant := (261537169329554568828537983763909105696596515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29752588654364219357/6250000000000000000)
  centralHi := (476041418469827509713/100000000000000000000)
  directionLo := (478566854857188406359/100000000000000000000)
  directionHi := (11964171371429710159/2500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree096.table
  base := (2934405269556756884567984630257908186127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-1002588257829523450126441028580000000000000)
      constant := (29124823864339662619137963739181868622791905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree096.table
  base := (585804447930998797320511487247262056877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-337266445545197676806707205420000000000000)
      constant := (9887304381360611301271410789965181551421925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478566854857188406359/100000000000000000000)
  centralHi := (11964171371429710159/2500000000000000000)
  directionLo := (240539517042957536697/50000000000000000000)
  directionHi := (96215806817183014679/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree097.table
  base := (398648185576569797589357716235052307421/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-4557414708050513752653210048645000000000000)
      constant := (133749239937483740452365063907734678246007340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree097.table
  base := (127362727293712316148550306517435651429/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-9198592663993722751102077941505000000000000)
      constant := (272432238877408816742756157404662720323572875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240539517042957536697/50000000000000000000)
  centralHi := (96215806817183014679/20000000000000000000)
  directionLo := (24178908138405094217/5000000000000000000)
  directionHi := (483578162768101884341/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree098.table
  base := (861074156440182214965702942186801161351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-4603182255868171979737435468680000000000000)
      constant := (136463746823331743869800351715459436313564770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree098.table
  base := (3439432450475490957809130760964875176731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-9290991298267108228423061336670000000000000)
      constant := (277962228286834253718417893613909758148858685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24178908138405094217/5000000000000000000)
  centralHi := (483578162768101884341/100000000000000000000)
  directionLo := (121516110551057344659/25000000000000000000)
  directionHi := (486064442204229378637/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree099.table
  base := (1849859365082857004327175588005371401059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-172183326062438155808209662545000000000000)
      constant := (5155749137021521930454632226239276857005295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree099.table
  base := (739019128421315926304995165801620347531/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-347532960464462729842372027105000000000000)
      constant := (10501747552064816425424785197597165508688275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121516110551057344659/25000000000000000000)
  centralHi := (486064442204229378637/100000000000000000000)
  directionLo := (244269034286196642979/50000000000000000000)
  directionHi := (488538068572393285959/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree100.table
  base := (1977716505065382749029476700559848902249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-4694717351503488433905886308750000000000000)
      constant := (141973678298062254697579658544575579601803615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree100.table
  base := (493879938520338756818059549759621209149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-9475788566813879183065028127000000000000000)
      constant := (289187103270531281924417307344990390905880920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244269034286196642979/50000000000000000000)
  centralHi := (488538068572393285959/100000000000000000000)
  directionLo := (9819984662179065683/2000000000000000000)
  directionHi := (490999233108953284151/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree101.table
  base := (842284356778962900688479183723447689169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-9480969798642293321980223457570000000000000)
      constant := (289538200850512718900102614006672827190189075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree101.table
  base := (4207246883912453149055316260382793993451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-9568187201087264660386011522165000000000000)
      constant := (294881984063939226106757551955459052189115885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/2000000000000000000)
  centralHi := (490999233108953284151/100000000000000000000)
  directionLo := (246724061140536133859/50000000000000000000)
  directionHi := (493448122281072267719/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree102.table
  base := (4467668410505834437193921844787186142787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-354537218306578139857358307320000000000000)
      constant := (10932703107992529228520465881117935930713935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree102.table
  base := (2231850812254980271480656229690592458691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-1073398426151183348634110546370000000000000)
      constant := (33403536011824409611472994385266217773760730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246724061140536133859/50000000000000000000)
  centralHi := (493448122281072267719/100000000000000000000)
  directionLo := (495884917951586678271/100000000000000000000)
  directionHi := (968525230374192731/195312500000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree103.table
  base := (4724157228530403665686626111748989601527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-9664039989912926230317125137710000000000000)
      constant := (300881703677687708284469579255521613596206145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree103.table
  base := (4720388544370995938442942925327234932181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-9752984469634035615027978312495000000000000)
      constant := (306436621347918791213709864401385551715844435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495884917951586678271/100000000000000000000)
  centralHi := (968525230374192731/195312500000000000)
  directionLo := (124577449384155109997/25000000000000000000)
  directionHi := (498309797536620439989/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree104.table
  base := (1245218374593342606211359911943633326071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-4877787542774121342242787988890000000000000)
      constant := (153317179073167815377601740539000780998039170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree104.table
  base := (622161670019171728918731073532927770243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-9845383103907421092348961707660000000000000)
      constant := (312296373860185345195055998282983561991862440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124577449384155109997/25000000000000000000)
  centralHi := (498309797536620439989/100000000000000000000)
  directionLo := (250361467078164534783/50000000000000000000)
  directionHi := (500722934156329069567/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree105.table
  base := (5237803347994870569264659461032936730091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-1094123353464839904294891868650000000000000)
      constant := (34715660605446297213624946039302994050951365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree105.table
  base := (5234402637127409343778069484642704393881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-368065990302992835913701670475000000000000)
      constant := (11785595549241882999584382093226338521969405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250361467078164534783/50000000000000000000)
  centralHi := (500722934156329069567/100000000000000000000)
  directionLo := (503124496779136425363/100000000000000000000)
  directionHi := (125781124194784106341/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree106.table
  base := (4395946977459604103275058569965893763/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-4969322638409437796411238828960000000000000)
      constant := (159150731911614418462901433333461872286253125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree106.table
  base := (5491703738734752068529432878359592810603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-10030180372454192046990928497990000000000000)
      constant := (324180737550019901289905065784394045029431405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503124496779136425363/100000000000000000000)
  centralHi := (125781124194784106341/25000000000000000000)
  directionLo := (126378662589951043357/25000000000000000000)
  directionHi := (505514650359804173429/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree107.table
  base := (5752252332684296617669346941736470908841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-10030180372454192046990928497990000000000000)
      constant := (324215911610203089804038954182949923572693535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree107.table
  base := (2874592389572991251761151679921368108067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-10122579006727577524311911893155000000000000)
      constant := (330205345417065554465655225304540144389178090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126378662589951043357/25000000000000000000)
  centralHi := (505514650359804173429/100000000000000000000)
  directionLo := (101578711194330648329/20000000000000000000)
  directionHi := (253946777985826620823/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree108.table
  base := (5868894156780425140040119868989383429/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-187439175334990898169618135890000000000000)
      constant := (6114523837940652526832742721016612821578240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree108.table
  base := (6006834578638638049160531801379982162263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-378332505222257888949366492160000000000000)
      constant := (12454996367459454372780863516492899910811315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101578711194330648329/20000000000000000000)
  centralHi := (253946777985826620823/50000000000000000000)
  directionLo := (127565342733309295439/25000000000000000000)
  directionHi := (510261370933237181757/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree109.table
  base := (6267408689936041555415960070706992176323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-10213250563724824955327830178130000000000000)
      constant := (336206589269737496494222460397964943943803605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree109.table
  base := (1252928524325589987741187524010078120957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-10307376275274348478953878683485000000000000)
      constant := (342419405643435098304679680328004177731645975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127565342733309295439/25000000000000000000)
  centralHi := (510261370933237181757/100000000000000000000)
  directionLo := (102523649785949869711/20000000000000000000)
  directionHi := (128154562232437337139/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree110.table
  base := (6525225309890845420881479183053600180049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-10304785659360141409496281018200000000000000)
      constant := (342282816290228635112369627108162236024306615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree110.table
  base := (6522599017192553468300468640250693344817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-10399774909547733956274862078650000000000000)
      constant := (348608855247880660949423484408921343601550295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102523649785949869711/20000000000000000000)
  centralHi := (128154562232437337139/25000000000000000000)
  directionLo := (514964340129429031521/100000000000000000000)
  directionHi := (257482170064714515761/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree111.table
  base := (3391593918107630749259075527436256192959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (37)
      square := (1439231063448371920887591825000000000000)
      linear := (-192524458425841812290087627005000000000000)
      constant := (6452091981645235019793275482346431280964795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree111.table
  base := (6780694461946819578335574489339208817839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-1165797060424568825955093941535000000000000)
      constant := (39428138830976099564029730320861463132267585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514964340129429031521/100000000000000000000)
  centralHi := (257482170064714515761/50000000000000000000)
  directionLo := (129324947823804010339/25000000000000000000)
  directionHi := (517299791295216041357/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree112.table
  base := (1760321799001160545845712318537112088349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-5243927925315387158916591349170000000000000)
      constant := (177298520100368768468478442573989020263854230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree112.table
  base := (7038920205120281957913292705436511164003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-10584572178094504910916828868980000000000000)
      constant := (361152587154793790733240720832145929007140405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129324947823804010339/25000000000000000000)
  centralHi := (517299791295216041357/100000000000000000000)
  directionLo := (64953093236486084389/12500000000000000000)
  directionHi := (519624745891888675113/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree113.table
  base := (456219678140000505428603119566136915237/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-5289695473133045386000816769205000000000000)
      constant := (180417517356572805249633117340859177868455960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree113.table
  base := (1824317003928233489143327064367606050923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-10676970812367890388237812264145000000000000)
      constant := (367506867164722344022530785712904882267498420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64953093236486084389/12500000000000000000)
  centralHi := (519624745891888675113/100000000000000000000)
  directionLo := (104387868837781275783/20000000000000000000)
  directionHi := (130484836047226594729/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree114.table
  base := (7557862762353103042651360273416279857259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (318)
      previous := (0)
      next := (222)
      square := (8635386380690231525325550950000000000000)
      linear := (-1185658449100156358463342708720000000000000)
      constant := (40791883273458910797035068181519244197858885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree114.table
  base := (3777865075801487601061588325129727824083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-398865535060787995020696135530000000000000)
      constant := (13848744017162374551625621760117797278240830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104387868837781275783/20000000000000000000)
  centralHi := (130484836047226594729/25000000000000000000)
  directionLo := (262121861679582861859/50000000000000000000)
  directionHi := (524243723359165723719/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree115.table
  base := (7816323368642636106399549011583725588201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-10762461137536723680338535218550000000000000)
      constant := (373472783423591622681615823772451302954407135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree115.table
  base := (1562859866098185706758871912807133125887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-10861768080914661342879779054475000000000000)
      constant := (380380250067668667930619973589804189859973725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262121861679582861859/50000000000000000000)
  centralHi := (524243723359165723719/100000000000000000000)
  directionLo := (526538017573866439943/100000000000000000000)
  directionHi := (65817252196733304993/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree116.table
  base := (1614977910086535904899231167890014066263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-10853996233172040134506986058620000000000000)
      constant := (379872535639508636777430046959157759494727525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree116.table
  base := (4036484351285475732404479899986082846571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-10954166715188046820200762449640000000000000)
      constant := (386899351052852220397000327790934242368574170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526538017573866439943/100000000000000000000)
  centralHi := (65817252196733304993/12500000000000000000)
  directionLo := (528822358093673159721/100000000000000000000)
  directionHi := (264411179046836579861/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree117.table
  base := (8333554607870615546902857736897557833297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-405390049215087281062053218470000000000000)
      constant := (14308377970533375409796411466150987789166485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree117.table
  base := (833173182482665900486200840151342313029/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-409132049980053048056360957215000000000000)
      constant := (14573088538856576234049691826571692115651450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528822358093673159721/100000000000000000000)
  centralHi := (264411179046836579861/50000000000000000000)
  directionLo := (531096873356348134403/100000000000000000000)
  directionHi := (132774218339087033601/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree118.table
  base := (8592312235268069988399542429705226814109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-11037066424442673042843887738760000000000000)
      constant := (392833791267001190027830296496188205619904715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree118.table
  base := (42952913184274404208122370851284320101/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-11138963983734817774842729239970000000000000)
      constant := (400102367738340253705479608957524176642727000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531096873356348134403/100000000000000000000)
  centralHi := (132774218339087033601/25000000000000000000)
  directionLo := (533361689061020477939/100000000000000000000)
  directionHi := (26668084453051023897/5000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree119.table
  base := (8851156497893959016564568967540168136087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-11128601520077989497012338578830000000000000)
      constant := (399395293026120102350034686161197422698371745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree119.table
  base := (8849515438126518663253207352729586263309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-11231362618008203252163712635135000000000000)
      constant := (406786281850918878283315291494480869145546715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533361689061020477939/100000000000000000000)
  centralHi := (26668084453051023897/5000000000000000000)
  directionLo := (535616928249248386119/100000000000000000000)
  directionHi := (13390423206231209653/2500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree120.table
  base := (9110081810134128838162203021346340859693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-415560615396789109302992200700000000000000)
      constant := (15037433693618517121075164979506731704298465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree120.table
  base := (9108524866599070476134332893565971329431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-1258195694697954303276077336700000000000000)
      constant := (45947236906998632698190094866203489569941465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535616928249248386119/100000000000000000000)
  centralHi := (13390423206231209653/2500000000000000000)
  directionLo := (537862711383022253377/100000000000000000000)
  directionHi := (268931355691511126689/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree121.table
  base := (4684541457468552793950819015259840133819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-5655835855674311202674620129485000000000000)
      constant := (206340020331019410406500171233479828418065565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree121.table
  base := (4683802939300234253496619758502816343861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-11416159886554974206805679425465000000000000)
      constant := (420318917993650972557274223339348135412842470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537862711383022253377/100000000000000000000)
  centralHi := (268931355691511126689/50000000000000000000)
  directionLo := (108019831283969722513/20000000000000000000)
  directionHi := (270049578209924306283/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree122.table
  base := (601759679029388339664948815381597409221/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-5701603403491969429758845549520000000000000)
      constant := (209701642580589633372371475836961125201958680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree122.table
  base := (1925350745981730965490577611830932271487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-11508558520828359684126662820630000000000000)
      constant := (427167638702438735283674499837905379283253725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108019831283969722513/20000000000000000000)
  centralHi := (270049578209924306283/50000000000000000000)
  directionLo := (67790797360630915187/12500000000000000000)
  directionHi := (542326378885047321497/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree123.table
  base := (2471823250478695060529338436160167758247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 75000000000000000000000000000000000000000
      center := (159)
      previous := (0)
      next := (111)
      square := (4317693190345115762662775475000000000000)
      linear := (-638596772367736406315896774395000000000000)
      constant := (23676691255358376629214584582994555032747410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree123.table
  base := (2471490989488953051523103148288029914039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-429665079818583154127690600585000000000000)
      constant := (16076714580996456560617402458939885598280780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67790797360630915187/12500000000000000000)
  centralHi := (542326378885047321497/100000000000000000000)
  directionLo := (544544491941387378591/100000000000000000000)
  directionHi := (17017015373168355581/3125000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree124.table
  base := (2536623236083337136394738315447409451517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-5793138499127285883927296389590000000000000)
      constant := (216505756188078400899308416270106800551909590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree124.table
  base := (10145232365090393804445294763463585392463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-11693355789375130638768629610960000000000000)
      constant := (441029882380364789293067343021765584027982505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544544491941387378591/100000000000000000000)
  centralHi := (17017015373168355581/3125000000000000000)
  directionLo := (34172100403511258573/6250000000000000000)
  directionHi := (546753606456180137169/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree125.table
  base := (650359410409110040337605119679836268793/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-5838906046944944111011521809625000000000000)
      constant := (219948246971699006436778435812847973170296440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree125.table
  base := (520227750141703505170786304429025378441/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-11785754423648516116089613006125000000000000)
      constant := (448043404249775547267788995584067743521790700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34172100403511258573/6250000000000000000)
  centralHi := (546753606456180137169/100000000000000000000)
  directionLo := (109790766213188494833/20000000000000000000)
  directionHi := (274476915532971237083/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree126.table
  base := (10665061985954704868359341977364295583669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-435901747760192765784870165160000000000000)
      constant := (16549458769408287980548040853972821477918345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree126.table
  base := (213278563141488996770227654096948381817/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (73)
      square := (2878462126896743841775183650000000000000)
      linear := (-439931594737848207163355422270000000000000)
      constant := (16855994770138201045930680013210737095454250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109790766213188494833/20000000000000000000)
  centralHi := (274476915532971237083/50000000000000000000)
  directionLo := (551145272238736627549/100000000000000000000)
  directionHi := (11022905444774732551/2000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree127.table
  base := (10924423548264809236307392047317975872021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2862)
      previous := (0)
      next := (1998)
      square := (77718477426212083727929958550000000000000)
      linear := (-11860882285160521130359945299390000000000000)
      constant := (453828190374704214385288013745663426742722835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree127.table
  base := (2730837083534486951459223100217033501311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-11970551692195287070731579796455000000000000)
      constant := (462235245540586498207559562091093573090707940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551145272238736627549/100000000000000000000)
  centralHi := (11022905444774732551/2000000000000000000)
  directionLo := (110665606866857584423/20000000000000000000)
  directionHi := (138332008583571980529/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree128.table
  base := (5591915907021330914347688222965549040737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 675000000000000000000000000000000000000000
      center := (1431)
      previous := (0)
      next := (999)
      square := (38859238713106041863964979275000000000000)
      linear := (-5976208690397918792264198069730000000000000)
      constant := (230437452140557909497877646087124349120499495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree128.table
  base := (5591406123845239702989543033984509019111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1350000000000000000000000000000000000000000
      center := (2889)
      previous := (0)
      next := (1971)
      square := (77718477426212083727929958550000000000000)
      linear := (-12062950326468672548052563191620000000000000)
      constant := (469413564046685655749161822957607817435159970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell172.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110665606866857584423/20000000000000000000)
  centralHi := (138332008583571980529/25000000000000000000)
  directionLo := (555502219661976432727/100000000000000000000)
  directionHi := (69437777457747054091/12500000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree129.table
  base := (11443283546068236183191430340403782306377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (106)
      previous := (0)
      next := (74)
      square := (2878462126896743841775183650000000000000)
      linear := (-446072313941894594025809147390000000000000)
      constant := (17332426965045699471621634688540518911531885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree129.table
  base := (11442316806416772160602106352276204731121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 150000000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (219)
      square := (8635386380690231525325550950000000000000)
      linear := (-1350594328971339780597060731865000000000000)
      constant := (52960757099411259897817755801495518070966815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell172.Kernel129
