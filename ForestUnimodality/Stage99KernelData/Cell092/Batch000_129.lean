import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell092.Parameters
import ForestUnimodality.BinomialMassData.Q107_207.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_207.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_207.Batch100_149
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch000_049
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch050_099
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree000.table
  base := (244550310330618400850255511/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (98)
      previous := (49)
      next := (49)
      square := (936568526964246667043667570000000000000)
      linear := (-37089188201078300208268779000000000000)
      constant := (489100620661236801700511022000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree000.table
  base := (244550310330618400850255511/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (98)
      previous := (49)
      next := (49)
      square := (936568526964246667043667570000000000000)
      linear := (-37089188201078300208268779000000000000)
      constant := (489100620661236801700511022000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree001.table
  base := (137540762107130639351083979847067952323559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-14359115744230067647441498309077000000000000)
      constant := (3932837497517186958157163600043010126074786394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree001.table
  base := (274842063136299563734556585176008349834781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-269923986603003120706241110543463250000000000)
      constant := (73785881028748904716120744930540013474175268543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9993880929153331779/20000000000000000000)
  directionHi := (3123087790360416181/6250000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree002.table
  base := (3239076815901096860034586402107429565993/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-28188486613384133933008293647697000000000000)
      constant := (2328031397782363658229219109200974824553900950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree002.table
  base := (161701641305890545115928369853820556640591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-529900541662912438061723909752789500000000000)
      constant := (43648230610925816522993397439436885471426427973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9993880929153331779/20000000000000000000)
  centralHi := (3123087790360416181/6250000000000000000)
  directionLo := (35333704876876176181/50000000000000000000)
  directionHi := (70667409753752352363/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree003.table
  base := (50390293898372446187932981369409923618549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-4668650831393133357619454331813000000000000)
      constant := (163604327014001551260972815667936097565274526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree003.table
  base := (10057727544291282368152887796595093608057/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-263292365574273918472402236320705250000000000)
      constant := (9198659140229951177396958961987584331851538570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35333704876876176181/50000000000000000000)
  centralHi := (70667409753752352363/100000000000000000000)
  directionLo := (21637386917609037587/25000000000000000000)
  directionHi := (86549547670436150349/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree004.table
  base := (8320499130663167305271221652641071003323/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-55847228351692266504141884324937000000000000)
      constant := (1009016953586523247149837197879767337123699272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree004.table
  base := (33206920390531655222538953110595701223921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-1049853651782731072772689508171442000000000000)
      constant := (18909261830344228368325873906805733835718567926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21637386917609037587/25000000000000000000)
  centralHi := (86549547670436150349/100000000000000000000)
  directionLo := (99938809291533317791/100000000000000000000)
  directionHi := (3123087790360416181/3125000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree005.table
  base := (23252781159204358368935284618929257562891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-69676599220846332789708679663557000000000000)
      constant := (754964536186388340710718165808868171541544306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree005.table
  base := (46397141425269118427761837459544651005541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-1309830206842640390128172307380768250000000000)
      constant := (14151278058242707525019639938803070869576612823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99938809291533317791/100000000000000000000)
  centralHi := (3123087790360416181/3125000000000000000)
  directionLo := (27933746395782012037/25000000000000000000)
  directionHi := (111734985583128048149/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree006.table
  base := (34023913972504931196536648607507262050259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-9278441121111155452808386111353000000000000)
      constant := (68475535212309246657172693615592024873761033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree006.table
  base := (16972302830047048228985443835601900775647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-523268920634183235827885035530031500000000000)
      constant := (3852186874196722983197638693724176468737234894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27933746395782012037/25000000000000000000)
  centralHi := (111734985583128048149/100000000000000000000)
  directionLo := (122399544132787517989/100000000000000000000)
  directionHi := (12239954413278751799/10000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree007.table
  base := (12857441455594081296077752580724257347757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-97335340959154465360842270340797000000000000)
      constant := (544341105687743568756208802467658135396026462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree007.table
  base := (25654877877077502141995746347582025318473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-1829783316962459024839137905799420750000000000)
      constant := (10212855745130616149825684127579596209927914019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122399544132787517989/100000000000000000000)
  centralHi := (12239954413278751799/10000000000000000000)
  directionLo := (66103308927327090863/50000000000000000000)
  directionHi := (132206617854654181727/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree008.table
  base := (19799164612420203557159579453474454454117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-111164711828308531646409065679417000000000000)
      constant := (513734596028997671404714394020671632968153111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree008.table
  base := (4937946909586685920737001578132629601143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-2089759872022368342194620705008747000000000000)
      constant := (9643789185915306388017082608159633627661424116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66103308927327090863/50000000000000000000)
  centralHi := (132206617854654181727/100000000000000000000)
  directionLo := (5653392780300188189/4000000000000000000)
  directionHi := (70667409753752352363/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree009.table
  base := (15331621854628774960159895840031952873447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-4629410470276392515999105963631000000000000)
      constant := (18924477518475135741720084373425903070053463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree009.table
  base := (15292635409642574758178290534650706992439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-783245475694092553183367834739357750000000000)
      constant := (3198842033919102340897860218320149988643539039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5653392780300188189/4000000000000000000)
  centralHi := (70667409753752352363/50000000000000000000)
  directionLo := (149908213937299976687/100000000000000000000)
  directionHi := (9369263371081248543/6250000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree010.table
  base := (2359560216844378793425418814656416061343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-138823453566616664217542656356657000000000000)
      constant := (528672056491282258802951102233257953020810345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree010.table
  base := (11764619315585098608271766344861516293061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-2609712982142186976905586303427399500000000000)
      constant := (9933531491274103603289841901636493723097839383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149908213937299976687/100000000000000000000)
  centralHi := (9369263371081248543/6250000000000000000)
  directionLo := (158017132003221933973/100000000000000000000)
  directionHi := (79008566001610966987/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree011.table
  base := (8907626287698685321153919322192828333701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-152652824435770730503109451695277000000000000)
      constant := (562724930805525451439834545721317167090251383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree011.table
  base := (8878700590240500401570648766185085810291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-2869689537202096294261069102636725750000000000)
      constant := (10577284290325949190510753444007371780514977073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158017132003221933973/100000000000000000000)
  centralHi := (79008566001610966987/50000000000000000000)
  directionLo := (1035811038796562427/625000000000000000)
  directionHi := (165729766207449988321/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree012.table
  base := (3244798392358314891863258287514237849243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-18498021700547199643186249670433000000000000)
      constant := (67852219080469560072599913046006190933497282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree012.table
  base := (323199898454259847835033461566238890921/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-1043222030754001870538850633948684000000000000)
      constant := (3827317877041275068120730776506141336744566420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1035811038796562427/625000000000000000)
  centralHi := (165729766207449988321/100000000000000000000)
  directionLo := (21637386917609037587/12500000000000000000)
  directionHi := (173099095340872300697/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree013.table
  base := (2218130456067693121645906253292386453989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-180311566174078863074243042372517000000000000)
      constant := (670972447142750534347332571007581311444649774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree013.table
  base := (1103354019675184026751917584099573057/2500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-20057057084745058751313814799144250000000000)
      constant := (74667551557578594783378778579740863203336000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21637386917609037587/12500000000000000000)
  centralHi := (173099095340872300697/100000000000000000000)
  directionLo := (180167250654720169073/100000000000000000000)
  directionHi := (90083625327360084537/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree014.table
  base := (1337945746279511927308879768262076552893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-194140937043232929359809837711137000000000000)
      constant := (742607877786352852259185270911932478809941438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree014.table
  base := (165964169124931864640796045594583787721/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-3649619202381824246327517500264704500000000000)
      constant := (13968687955311924477481485381257149958640165808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180167250654720169073/100000000000000000000)
  centralHi := (90083625327360084537/50000000000000000000)
  directionLo := (93484196002764461579/50000000000000000000)
  directionHi := (186968392005528923159/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree015.table
  base := (144698178623022591958476594843640257361/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-23107811990265221738375181449973000000000000)
      constant := (91649912746725997403092149581479856707455256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree015.table
  base := (569617715977574530357624402904335929561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-1303198585813911187894333433158010250000000000)
      constant := (5172648547267201527093901464492884705689865922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93484196002764461579/50000000000000000000)
  centralHi := (186968392005528923159/100000000000000000000)
  directionLo := (193530672012953797571/100000000000000000000)
  directionHi := (48382668003238449393/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree016.table
  base := (-78364722905124569864591111816900983381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-221799678781541061930943428388377000000000000)
      constant := (917152673180874850081462198720910406508738354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree016.table
  base := (-43292784474956350797607728550192656671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-4169572312501642881038483098683357000000000000)
      constant := (17256393966262978743307233887730387715611471148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193530672012953797571/100000000000000000000)
  centralHi := (48382668003238449393/25000000000000000000)
  directionLo := (99938809291533317791/50000000000000000000)
  directionHi := (199877618583066635583/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree017.table
  base := (-324177153966780513726460954093100671969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-235629049650695128216510223726997000000000000)
      constant := (1019094683888791356325244039685411972409067092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree017.table
  base := (-1311416232234565435996909049569643433539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-4429548867561552198393965897892683250000000000)
      constant := (19176087889897455344079993170962034695632039583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99938809291533317791/50000000000000000000)
  centralHi := (199877618583066635583/100000000000000000000)
  directionLo := (103014566701862886839/50000000000000000000)
  directionHi := (206029133403725773679/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree018.table
  base := (-1143065000878939769705728846002662902401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-9239200759994414611188037743171000000000000)
      constant := (41864282474250429481208237846887182649259742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree018.table
  base := (-574814739516149952645851883828410173603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-1563175140873820505249816232367336500000000000)
      constant := (7090218382975382840042485427512193614528872788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103014566701862886839/50000000000000000000)
  centralHi := (206029133403725773679/100000000000000000000)
  directionLo := (212002229261257057087/100000000000000000000)
  directionHi := (3312534832207141517/1562500000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree019.table
  base := (-3144433394533825889984624679476521931653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-263287791389003260787643814404237000000000000)
      constant := (1250597843393199789813279909622729837250200201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree019.table
  base := (-3156126691182760265492090776595552287149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-4949501977681370833104931496311335750000000000)
      constant := (23534885262879293420677399102496150425867276753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212002229261257057087/100000000000000000000)
  centralHi := (3312534832207141517/1562500000000000000)
  directionLo := (108905792559894357199/50000000000000000000)
  directionHi := (217811585119788714399/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree020.table
  base := (-3887712782709103468570871268667925507719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-277117162258157327073210609742857000000000000)
      constant := (1379651463216158442431548548100756019973249523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree020.table
  base := (-3898103778660339971296154746917095792067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-5209478532741280150460414295520662000000000000)
      constant := (25964464361619328003502578751159662282280254399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108905792559894357199/50000000000000000000)
  centralHi := (217811585119788714399/100000000000000000000)
  directionLo := (223469971166256096297/100000000000000000000)
  directionHi := (111734985583128048149/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree021.table
  base := (-1132349462479657957788961814946027523653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-32327392569701265928753045009053000000000000)
      constant := (168589407789142221981031700133745617279850756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree021.table
  base := (-181544451622920201696944058631165635069/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-1823151695933729822605299031576662750000000000)
      constant := (9518597624629582796571687267630308221792408275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223469971166256096297/100000000000000000000)
  centralHi := (111734985583128048149/50000000000000000000)
  directionLo := (57247144805275931779/25000000000000000000)
  directionHi := (228988579221103727117/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree022.table
  base := (-5080749915640537882120987954753251690783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-304775903996465459644344200420097000000000000)
      constant := (1663396618625458369431210128514153306100546411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree022.table
  base := (-5088902210547074958753935959518500754499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-5729431642861098785171379893939314500000000000)
      constant := (31305852715720024815852725371111325260891104703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57247144805275931779/25000000000000000000)
  centralHi := (228988579221103727117/100000000000000000000)
  directionLo := (23437728305949803413/10000000000000000000)
  directionHi := (234377283059498034131/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree023.table
  base := (-5551240318007306250685610353933960808487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (2646)
      previous := (1323)
      next := (1323)
      square := (25287350228034660010179024390000000000000)
      linear := (-602278402392475474347657836973000000000000)
      constant := (3436279829230902229259326134812783058170851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree023.table
  base := (-5558439571310294135352276224597580780809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (49686)
      previous := (24843)
      next := (24843)
      square := (474840243170873060191139457990000000000000)
      linear := (-11322132699283569191922235714836750000000000)
      constant := (64673168002545327120154744071485174981629837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23437728305949803413/10000000000000000000)
  centralHi := (234377283059498034131/100000000000000000000)
  directionLo := (239644846001336800549/100000000000000000000)
  directionHi := (4792896920026736011/2000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree024.table
  base := (-5948849431243658761906559498392763220243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-36937182859419288023941976788593000000000000)
      constant := (220041879947810558393657619320842684769474359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree024.table
  base := (-119103909203098418915391860803960543861/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-2083128250993639139960781830785989000000000000)
      constant := (12424138069680020836426991171705022170914136950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239644846001336800549/100000000000000000000)
  centralHi := (4792896920026736011/2000000000000000000)
  directionLo := (122399544132787517989/50000000000000000000)
  directionHi := (244799088265575035979/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree025.table
  base := (-6280308784705061362697550663804831713177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-346264016603927658501044586435957000000000000)
      constant := (2151055141793117488105646678946550588640692909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree025.table
  base := (-6285893220795581420559788969964719360173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-6509361308040826737237828291567293250000000000)
      constant := (40484974501846484358737418745732304521881020881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122399544132787517989/50000000000000000000)
  centralHi := (244799088265575035979/100000000000000000000)
  directionLo := (124923511614416647239/50000000000000000000)
  directionHi := (249847023228833294479/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree026.table
  base := (-6551300277425500430800290571356874117677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-360093387473081724786611381774577000000000000)
      constant := (2329745541887712239533083043394151766977219409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree026.table
  base := (-6556206775238794270464255113221004037877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-40055253627815006240197107046015500000000000)
      constant := (259457189283206090279019065021630485341889201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124923511614416647239/50000000000000000000)
  centralHi := (249847023228833294479/100000000000000000000)
  directionLo := (254794969371378151593/100000000000000000000)
  directionHi := (127397484685689075797/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree027.table
  base := (-6766621772917261973085628152216380935169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-13848991049712436706376969522711000000000000)
      constant := (93199244145538270325521901183204534485295599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree027.table
  base := (-6770926317931985661953530829668951513977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-2343104806053548457316264629995315250000000000)
      constant := (15787000308521571388135161725331544886011442223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254794969371378151593/100000000000000000000)
  centralHi := (127397484685689075797/50000000000000000000)
  directionLo := (64912160752827112761/25000000000000000000)
  directionHi := (51929728602261690209/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree028.table
  base := (-1732581406732568628743491681402150356419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-387752129211389857357744972451817000000000000)
      constant := (2710899412121404436745091923995168345837069692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree028.table
  base := (-6934096922166557747660295484920150013493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-7289290973220554689304276689195272000000000000)
      constant := (51022097411163165148948665803854427630931136921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64912160752827112761/25000000000000000000)
  centralHi := (51929728602261690209/20000000000000000000)
  directionLo := (264413235709308363453/100000000000000000000)
  directionHi := (132206617854654181727/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree029.table
  base := (-281833401083205944341549732237010828327/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-401581500080543923643311767790437000000000000)
      constant := (2913256109074611887885819918663532358475136475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree029.table
  base := (-7049134934754948064361238957919518627853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-7549267528280464006659759488404598250000000000)
      constant := (54830638171193046026107645316632266806391441841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264413235709308363453/100000000000000000000)
  centralHi := (132206617854654181727/50000000000000000000)
  directionLo := (269093479331845999383/100000000000000000000)
  directionHi := (33636684916480749923/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree030.table
  base := (-7116041931970691260740594076087207925709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-46156763438855332214319840347673000000000000)
      constant := (347045375216046386303428505483439601021899817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree030.table
  base := (-355946297412974800898169192712733119247/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-2603081361113457774671747429204641500000000000)
      constant := (19595283093690786560066647510147246584373979060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269093479331845999383/100000000000000000000)
  centralHi := (33636684916480749923/12500000000000000000)
  directionLo := (273693701095898435723/100000000000000000000)
  directionHi := (68423425273974608931/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree031.table
  base := (-3571694819871624864184164942410211299631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-429240241818852056214445358467677000000000000)
      constant := (3341321318103468340411487230705086904014740854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree031.table
  base := (-1429181476827724348651531680793268482247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-8069220638400282641370725086823250750000000000)
      constant := (62887077017053693455814226121201224214717039295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273693701095898435723/100000000000000000000)
  centralHi := (68423425273974608931/25000000000000000000)
  directionLo := (139108935209266269429/50000000000000000000)
  directionHi := (278217870418532538859/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree032.table
  base := (-1425988491887574417466997094174910607651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-443069612688006122500012153806297000000000000)
      constant := (3566965448025745472259446087552362758954603835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree032.table
  base := (-1426427632806589002545261027087307744257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-8329197193460191958726207886032577000000000000)
      constant := (67133769170176268208111441196071088005335199145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139108935209266269429/50000000000000000000)
  centralHi := (278217870418532538859/100000000000000000000)
  directionLo := (5653392780300188189/2000000000000000000)
  directionHi := (282669639015009409451/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree033.table
  base := (-442340283180011793957503530165442011853/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-50766553728573354309508772127213000000000000)
      constant := (422257317240235488195748098171858096435028624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree033.table
  base := (-3539678759254502513969705145398898221693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-2863057916173367092027230228413967750000000000)
      constant := (23841819757861482141204295304884218707977348214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5653392780300188189/2000000000000000000)
  centralHi := (282669639015009409451/100000000000000000000)
  directionLo := (287052375397814982539/100000000000000000000)
  directionHi := (14352618769890749127/5000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree034.table
  base := (-1746842374780582493011463441490299035507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-470728354426314255071145744483537000000000000)
      constant := (4041351491440310526476245852877274235503414076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree034.table
  base := (-87362933030052385582692100854185908427/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-8849150303580010593437173484451229500000000000)
      constant := (76061753284815255844871313797783361862922265520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287052375397814982539/100000000000000000000)
  centralHi := (14352618769890749127/5000000000000000000)
  directionLo := (145684597351762330023/50000000000000000000)
  directionHi := (291369194703524660047/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree035.table
  base := (-1715240618370624690377092261454257604901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-484557725295468321356712539822157000000000000)
      constant := (4290054572963926978839398245735840354516796068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree035.table
  base := (-6862410629381627217750746788071440224203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-9109126858639919910792656283660555750000000000)
      constant := (80742318338824965424831598232327896103485582791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145684597351762330023/50000000000000000000)
  centralHi := (291369194703524660047/100000000000000000000)
  directionLo := (9238218268698255049/3125000000000000000)
  directionHi := (295622984598344161569/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree036.table
  base := (-837409434206611494277814683528918884971/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-18458781339430458801565901302251000000000000)
      constant := (168385558286507596399193686262661615278802728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree036.table
  base := (-6700533890204714984387387854132419668289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-3123034471233276409382713027623294000000000000)
      constant := (28522291082900532922395796076058580924235295111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9238218268698255049/3125000000000000000)
  centralHi := (295622984598344161569/100000000000000000000)
  directionLo := (149908213937299976687/50000000000000000000)
  directionHi := (2398531422996799627/800000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree037.table
  base := (-6503197375916975979215613383336263294817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-512216467033776453927846130499397000000000000)
      constant := (4810405297935688147286942572082407151360128789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree037.table
  base := (-813036258668992150117359782535900709299/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-9629079968759738545503621882079208250000000000)
      constant := (90535180481939093281295796512836968912448542424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149908213937299976687/50000000000000000000)
  centralHi := (2398531422996799627/800000000000000000)
  directionLo := (303952022240579216167/100000000000000000000)
  directionHi := (37994002780072402021/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree038.table
  base := (-1568369803479205942346067233830489203221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-526045837902930520213412925838017000000000000)
      constant := (5082029518550366384664975063452002490841577828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree038.table
  base := (-784303414450702409242009836576909012107/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-9889056523819647862859104681288534500000000000)
      constant := (95647039382789582946149026657723001396556930232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303952022240579216167/100000000000000000000)
  centralHi := (37994002780072402021/12500000000000000000)
  directionLo := (38504012214798377307/12500000000000000000)
  directionHi := (308032097718387018457/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree039.table
  base := (-3005377777572487961081629253129589921837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-59986134308009398499886635686293000000000000)
      constant := (595697074672471539728796235633503681588089362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree039.table
  base := (-1202315525733340368860172225788819135751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-20017816723628317909693466430962250000000000)
      constant := (199018304629264844929053076593224018698438605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38504012214798377307/12500000000000000000)
  centralHi := (308032097718387018457/100000000000000000000)
  directionLo := (312058831993972405137/100000000000000000000)
  directionHi := (156029415996986202569/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree040.table
  base := (-5715562562111276364941463151306506645023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-553704579641238652784546516515257000000000000)
      constant := (5648130100432192465154620355720169165589136491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree040.table
  base := (-5716274891371614117921611754294415540253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-10409009633939466497570070279707187000000000000)
      constant := (106300760485703794757631563197980579868857524641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312058831993972405137/100000000000000000000)
  centralHi := (156029415996986202569/50000000000000000000)
  directionLo := (158017132003221933973/50000000000000000000)
  directionHi := (316034264006443867947/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree041.table
  base := (-5388353252505449229503074174190451391529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-567533950510392719070113311853877000000000000)
      constant := (5942592333238549877677064164116784782774791293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree041.table
  base := (-5388970102259701483796607887267928673941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-10668986188999375814925553078916513250000000000)
      constant := (111842358539627890030588481781690077624300501977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158017132003221933973/50000000000000000000)
  centralHi := (316034264006443867947/100000000000000000000)
  directionLo := (319960306017398084187/100000000000000000000)
  directionHi := (79990076504349521047/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree042.table
  base := (-1005902078563675344685535762400909874719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-64595924597727420595075567465833000000000000)
      constant := (693850544824169647172848700153774780144104735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree042.table
  base := (-5030044243228646243014687653705600492057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-3642987581353095044093678626041946500000000000)
      constant := (39175657476107219370567245310676048766659612143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319960306017398084187/100000000000000000000)
  centralHi := (79990076504349521047/25000000000000000000)
  directionLo := (323838754363030792637/100000000000000000000)
  directionHi := (161919377181515396319/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree043.table
  base := (-579919674057566992775063510494120766597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-595192692248700851641246902531117000000000000)
      constant := (6554313191712513461435527212874440784725560392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree043.table
  base := (-4639819149473995135748246623310148583847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-11188939299119194449636518677335165750000000000)
      constant := (123354515834620147778616868640013807930303983059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323838754363030792637/100000000000000000000)
  centralHi := (161919377181515396319/50000000000000000000)
  directionLo := (327671299060585655357/100000000000000000000)
  directionHi := (163835649530292827679/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree044.table
  base := (-168726700338897628055884401744841171137/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-609022063117854917926813697869737000000000000)
      constant := (6871563295193200129488865345738828838816255725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree044.table
  base := (-4218566691877659679144301066657034646207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-11448915854179103766992001476544492000000000000)
      constant := (129324915841937217716700498700829911961783343979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327671299060585655357/100000000000000000000)
  centralHi := (163835649530292827679/50000000000000000000)
  directionLo := (1035811038796562427/312500000000000000)
  directionHi := (331459532414899976641/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree045.table
  base := (-29423215803293171489189277511336289177/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-23068571629148480896754833081791000000000000)
      constant := (266533404302683183530760513189997397187246976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree045.table
  base := (-1883258266922684343551251564873656414629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-3902964136413004361449161425251272750000000000)
      constant := (45146036951286153746959432569987512556064005542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1035811038796562427/312500000000000000)
  centralHi := (331459532414899976641/100000000000000000000)
  directionLo := (67040991349876828889/20000000000000000000)
  directionHi := (167602478374692072223/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree046.table
  base := (-3283564813645067661214340826528804566627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (2646)
      previous := (1323)
      next := (1323)
      square := (25287350228034660010179024390000000000000)
      linear := (-1203555396703521834589692416913000000000000)
      constant := (14232185762474888896524854699041722276701071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree046.table
  base := (-205241417744495301330261360772641777697/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (49686)
      previous := (24843)
      next := (24843)
      square := (474840243170873060191139457990000000000000)
      linear := (-22625461180149191685638879158720500000000000)
      constant := (267852644303804950232296242450683298649321936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67040991349876828889/20000000000000000000)
  centralHi := (167602478374692072223/50000000000000000000)
  directionLo := (16945449568395113949/5000000000000000000)
  directionHi := (338908991367902278981/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree047.table
  base := (-13852559537342708844123604472506629069/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-650510175725317116783514083885597000000000000)
      constant := (7868833997506247569493558175954406563401494600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree047.table
  base := (-21646633055240675333367945752501831169/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-12228845519358831719058449874172470750000000000)
      constant := (148092685834980572135869351346316831574435028704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16945449568395113949/5000000000000000000)
  centralHi := (338908991367902278981/100000000000000000000)
  directionLo := (21410811177440718859/6250000000000000000)
  directionHi := (68514595767810300349/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree048.table
  base := (-556788042605995959095455356421668742437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-73815505177163464785453431024913000000000000)
      constant := (912935901611708457897874574934699246823009924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree048.table
  base := (-69605438148706436344077302067769214267/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-4162940691472913678804644224460599000000000000)
      constant := (51544661572393430411741458025869656663210109856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21410811177440718859/6250000000000000000)
  centralHi := (68514595767810300349/20000000000000000000)
  directionLo := (21637386917609037587/6250000000000000000)
  directionHi := (346198190681744601393/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree049.table
  base := (-1653603271986773743579610010651491976901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-678168917463625249354647674562837000000000000)
      constant := (8571591938673485030201918192070667740093923017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree049.table
  base := (-1653794604905767087250228888255504952849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-12748798629478650353769415472591123250000000000)
      constant := (161317914116453375177951634190337462078568539653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21637386917609037587/6250000000000000000)
  centralHi := (346198190681744601393/100000000000000000000)
  directionLo := (34978583252036661227/10000000000000000000)
  directionHi := (349785832520366612271/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree050.table
  base := (-5249823170218955754713572746202844463/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-691998288332779315640214469901457000000000000)
      constant := (8934339049967763994665425968636046954506994200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree050.table
  base := (-8204137334007567611122519848423237029/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-13008775184538559671124898271800449500000000000)
      constant := (168144447535619888177439518809350622066316222464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34978583252036661227/10000000000000000000)
  centralHi := (349785832520366612271/100000000000000000000)
  directionLo := (353337048768761761813/100000000000000000000)
  directionHi := (176668524384380880907/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree051.table
  base := (-2602001628821730159957543909028650503/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-78425295466881486880642362804453000000000000)
      constant := (1033851472062094021221621105551232445064278240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree051.table
  base := (-52057799954510649731792148364884385473/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-4422917246532822996160127023669925250000000000)
      constant := (58371187530390658892022047592183465713747126616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353337048768761761813/100000000000000000000)
  centralHi := (176668524384380880907/50000000000000000000)
  directionLo := (44606615861829897363/12500000000000000000)
  directionHi := (71370585378927835781/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree052.table
  base := (123629435629532089664959102865735630693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-719657030071087448211348060578697000000000000)
      constant := (9682563520681510685715425879673266604026376238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree052.table
  base := (247136431837396778313930051784134738081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-80051646713954901217963691539758000000000000)
      constant := (1078255860204942076752198388263040546829334547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44606615861829897363/12500000000000000000)
  centralHi := (71370585378927835781/20000000000000000000)
  directionLo := (180167250654720169073/50000000000000000000)
  directionHi := (360334501309440338147/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree053.table
  base := (235178197835484274348475835320530839507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-733486400940241514496914855917317000000000000)
      constant := (10068039009781021023878974678072243567922713924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree053.table
  base := (235151840070768010932619545081255205761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-13788704849718287623191346669428428250000000000)
      constant := (189479464913076827426556299762229000645740369932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180167250654720169073/50000000000000000000)
  centralHi := (360334501309440338147/100000000000000000000)
  directionLo := (90945689230776431603/25000000000000000000)
  directionHi := (363782756923105726413/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree054.table
  base := (415997707341433226704691184774076602751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-27678361918866502991943764861331000000000000)
      constant := (387447740449403358163968623659175946091421116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree054.table
  base := (831950038157539280350072543622098053371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-4682893801592732313515609822879251500000000000)
      constant := (65625407571122869895424834550032033282388841542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90945689230776431603/25000000000000000000)
  centralHi := (363782756923105726413/100000000000000000000)
  directionLo := (367198632398362553967/100000000000000000000)
  directionHi := (22949914524897659623/6250000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree055.table
  base := (1208525086416315019063653668232504687713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-761145142678549647068048446594557000000000000)
      constant := (10861712856249213239883117584769114728909209558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree055.table
  base := (483394416224333321193648862009394154741/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-14308657959838106257902312267847080750000000000)
      constant := (204415502377201750039250062606754686725857502115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367198632398362553967/100000000000000000000)
  centralHi := (22949914524897659623/6250000000000000000)
  directionLo := (370583023135005687251/100000000000000000000)
  directionHi := (92645755783751421813/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree056.table
  base := (3199854648481116341277296520772367819479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-774974513547703713353615241933177000000000000)
      constant := (11269910085464294554207815679014343729565618557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree056.table
  base := (1599893736943344102107738339014884929183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-14568634514898015575257795067056407000000000000)
      constant := (212097294275869655150058414636724550365323336298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370583023135005687251/100000000000000000000)
  centralHi := (92645755783751421813/25000000000000000000)
  directionLo := (93484196002764461579/25000000000000000000)
  directionHi := (373936784011057846317/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree057.table
  base := (4012373692711272219023465544124439298801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-87644876046317531071020226363533000000000000)
      constant := (1298408915915470773532643664063696485167197187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree057.table
  base := (1003078981865207750733725121716316974193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-4942870356652641630871092622088577750000000000)
      constant := (73307196758513299332606713484693329698051813572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93484196002764461579/25000000000000000000)
  centralHi := (373936784011057846317/100000000000000000000)
  directionLo := (94315182976146824871/25000000000000000000)
  directionHi := (75452146380917459897/20000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree058.table
  base := (4854581481669641701189111688615606370711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-802633255286011845924748832610417000000000000)
      constant := (12109022960731941551019015632526042705792865213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree058.table
  base := (4854531823057369851143293292862519929551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-15088587625017834209968760665475059500000000000)
      constant := (227888383505177022536866086849755760401415366853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94315182976146824871/25000000000000000000)
  centralHi := (75452146380917459897/20000000000000000000)
  directionLo := (190277824008630377813/50000000000000000000)
  directionHi := (380555648017260755627/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree059.table
  base := (2863228098117404942853984327317960327581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-816462626155165912210315627949037000000000000)
      constant := (12539937926299897152837271165315337854717678846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree059.table
  base := (28632067596421677176734130004059124351/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-15348564180077743527324243464684385750000000000)
      constant := (235997668160494778421409268378929336826599750600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190277824008630377813/50000000000000000000)
  centralHi := (380555648017260755627/100000000000000000000)
  directionLo := (11994446250573638967/3125000000000000000)
  directionHi := (76764456003671289389/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree060.table
  base := (414248712561514534049360655025891851351/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-92254666336035553166209158143073000000000000)
      constant := (1442047208514440396449225689578797445889504592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree060.table
  base := (662794273465775099372126521718563155461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-5202846911712550948226575421297904000000000000)
      constant := (81416479779448106210666046724252149521613688610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11994446250573638967/3125000000000000000)
  centralHi := (76764456003671289389/20000000000000000000)
  directionLo := (193530672012953797571/50000000000000000000)
  directionHi := (387061344025907595143/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree061.table
  base := (7559135519466901008138918973369842368421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-844121367893474044781449218626277000000000000)
      constant := (13424483589243691039798463726222928458548157143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree061.table
  base := (1889776006494579332682739969370787069141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-15868517290197562162035209063103038250000000000)
      constant := (252643692896813261526492454008784789778156794492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193530672012953797571/50000000000000000000)
  centralHi := (387061344025907595143/100000000000000000000)
  directionLo := (19513676321992375903/5000000000000000000)
  directionHi := (390273526439847518061/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree062.table
  base := (4259955695423700694951517513028308428681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-857950738762628111067016013964897000000000000)
      constant := (13878113876164867351571939194564940658573701446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree062.table
  base := (1703976869537801685764180843213862965989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-16128493845257471479390691862312364500000000000)
      constant := (261180425337044076055905904675653740414085738835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19513676321992375903/5000000000000000000)
  centralHi := (390273526439847518061/100000000000000000000)
  directionLo := (393459485640449042533/100000000000000000000)
  directionHi := (196729742820224521267/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree063.table
  base := (2377573973825713209730471138853133515891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-32288152208584525087132696640871000000000000)
      constant := (531085762169224529487642073623216230519625356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree063.table
  base := (1188784084955188654601258949191084825453/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-5462823466772460265582058220507230250000000000)
      constant := (89953211234466641226188862428530719278655089224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393459485640449042533/100000000000000000000)
  centralHi := (196729742820224521267/50000000000000000000)
  directionLo := (396619853563962545179/100000000000000000000)
  directionHi := (19830992678198127259/5000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree064.table
  base := (1316284954688874800050773068954808190383/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-885609480500936243638149604642137000000000000)
      constant := (14808088562262888077496398776779660203065923112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree064.table
  base := (10530259712651203454531886688723836360087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-16648446955377290114101657460731017000000000000)
      constant := (278681315499129562748920925837745027083284413661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396619853563962545179/100000000000000000000)
  centralHi := (19830992678198127259/5000000000000000000)
  directionLo := (79951047433226654233/20000000000000000000)
  directionHi := (199877618583066635583/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree065.table
  base := (5789927339610533260732449949681980465763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-899438851370090309923716399980757000000000000)
      constant := (15284432713864308925472184906870570453984985858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree065.table
  base := (11579837582869188251381845852668650015647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-100049843257024848706846983786629250000000000)
      constant := (1702044192988906070894037281893155733512331789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79951047433226654233/20000000000000000000)
  centralHi := (199877618583066635583/50000000000000000000)
  directionLo := (100716554945799447367/25000000000000000000)
  directionHi := (402866219783197789469/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree066.table
  base := (12659014313295977117757620526057361491489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-101474246915471597356587021702153000000000000)
      constant := (1752038659730587325027673366781511032686993043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree066.table
  base := (2531799929478519143794571253799915201309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-5722800021832369582937541019716556500000000000)
      constant := (98917363756580045164482522745853294000811129545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100716554945799447367/25000000000000000000)
  centralHi := (402866219783197789469/100000000000000000000)
  directionLo := (202976681199501456741/50000000000000000000)
  directionHi := (405953362399002913483/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree067.table
  base := (2753550574558958454640354884569488378883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-927097593108398442494849990657997000000000000)
      constant := (16259834152454901660571617583266039012577929445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree067.table
  base := (2753548058942215078758272733380826936079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-17428376620557018066168105858358995750000000000)
      constant := (306001181957950680760621002834499996719623480185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202976681199501456741/50000000000000000000)
  centralHi := (405953362399002913483/100000000000000000000)
  directionLo := (409017204826042200393/100000000000000000000)
  directionHi := (204508602413021100197/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree068.table
  base := (3726516392415400349666464881108697891091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-940926963977552508780416785996617000000000000)
      constant := (16758891290115353560495291509569218127913811012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree068.table
  base := (7453027392290603571396019059551085352323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-17688353175616927383523588657568322000000000000)
      constant := (315392739408409255772669447808277343614498171138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409017204826042200393/100000000000000000000)
  centralHi := (204508602413021100197/50000000000000000000)
  directionLo := (103014566701862886839/25000000000000000000)
  directionHi := (412058266807451547357/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree069.table
  base := (16073948358429667957920375944309717247413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (294)
      previous := (147)
      next := (147)
      square := (2809705580892740001131002710000000000000)
      linear := (-200536932334952021647969666317000000000000)
      constant := (3626448076617357745657029223495929151742239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree069.table
  base := (4018484778190056598856466428610295449689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (16562)
      previous := (8281)
      next := (8281)
      square := (158280081056957686730379819330000000000000)
      linear := (-11309596553671604726451840867534750000000000)
      constant := (204742761529405128130735945797655380036489764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103014566701862886839/25000000000000000000)
  centralHi := (412058266807451547357/100000000000000000000)
  directionLo := (415077049046334639871/100000000000000000000)
  directionHi := (1621394722837244687/390625000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree070.table
  base := (3454279564212326408503393097973951786649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-968585705715860641351550376673857000000000000)
      constant := (17779718111614734048732723553685799766843538335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree070.table
  base := (4317847474184927265872611366720430520481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-18208306285736746018234554255986974500000000000)
      constant := (334603250467021821607318348800646492726288262572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415077049046334639871/100000000000000000000)
  centralHi := (1621394722837244687/390625000000000000)
  directionLo := (418074034168190907899/100000000000000000000)
  directionHi := (4180740341681909079/1000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree071.table
  base := (18498411069648123499599605737610640989813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-982415076585014707637117172012477000000000000)
      constant := (18301487705385825491580871203159349785257499079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree071.table
  base := (115615026745118859531973922630363959673/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-18468282840796655335590037055196300750000000000)
      constant := (344422202401640302652092270133287608085625919040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418074034168190907899/100000000000000000000)
  centralHi := (4180740341681909079/1000000000000000000)
  directionLo := (210524843810842207021/50000000000000000000)
  directionHi := (421049687621684414043/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree072.table
  base := (308671651003053360249276483692599955273/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-36897942498302547182321628420411000000000000)
      constant := (697438075527336449962008700924368664085722688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree072.table
  base := (9877489923282223098501732046760619286913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-6242753131952188217648506618135209000000000000)
      constant := (118127872567892526913080763162445985249738618226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210524843810842207021/50000000000000000000)
  centralHi := (421049687621684414043/100000000000000000000)
  directionLo := (16960178340900564567/4000000000000000000)
  directionHi := (3312534832207141517/781250000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree073.table
  base := (21041119543162199998517965135538420571291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1010073818323322840208250762689717000000000000)
      constant := (19367739083726515537130160628087946261019749353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree073.table
  base := (10520557279963783030191924522734709948321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-18988235950916473970301002653614953250000000000)
      constant := (364487495826308390660647369088152584222976574326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16960178340900564567/4000000000000000000)
  centralHi := (3312534832207141517/781250000000000000)
  directionLo := (53367347555589696927/12500000000000000000)
  directionHi := (426938780444717575417/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree074.table
  base := (22356810964768437237815705858994920484683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1023903189192476906493817558028337000000000000)
      constant := (19912220813973275329167652457674002449282727289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree074.table
  base := (1397300418566090673035417358388885129143/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-19248212505976383287656485452824279500000000000)
      constant := (374733836307619867217346129132883965001414640464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53367347555589696927/12500000000000000000)
  centralHi := (426938780444717575417/100000000000000000000)
  directionLo := (42985307216335574881/10000000000000000000)
  directionHi := (429853072163355748811/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree075.table
  base := (23702058457405795351345102930761600101619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-115303617784625663642153817040773000000000000)
      constant := (2273808134328820191931013000172843659361269353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree075.table
  base := (5925513700786644390487671789746245687373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-6502729687012097535003989417344535250000000000)
      constant := (128374212919142756127548410693643338513099834292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42985307216335574881/10000000000000000000)
  centralHi := (429853072163355748811/100000000000000000000)
  directionLo := (21637386917609037587/5000000000000000000)
  directionHi := (432747738352180751741/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree076.table
  base := (6269215194434568086053340683941617610097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1051561930930785039064951148705577000000000000)
      constant := (21023896250926266615271500488528644497300061804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree076.table
  base := (626921441232698481490037424814489358961/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-19768165616096201922367451051242932000000000000)
      constant := (395653902846142412169596534325400532206656683320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21637386917609037587/5000000000000000000)
  centralHi := (432747738352180751741/100000000000000000000)
  directionLo := (108905792559894357199/25000000000000000000)
  directionHi := (435623170239577428797/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree077.table
  base := (2648121687530044209677207529322600644177/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1065391301799939105350517944044197000000000000)
      constant := (21591089924870132311577864678837626050007800910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree077.table
  base := (13240607098749316377089258719292320725893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-20028142171156111239722933850452258250000000000)
      constant := (406327628295356077836101967661125934302230860558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108905792559894357199/25000000000000000000)
  centralHi := (435623170239577428797/100000000000000000000)
  directionLo := (109619936556447222007/25000000000000000000)
  directionHi := (438479746225788888029/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree078.table
  base := (13957562931292855604382118748769557269119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-119913408074343685737342748820313000000000000)
      constant := (2462872690901635793640259866347248574772183706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree078.table
  base := (5583024714177823348893318552454925062137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-40016013266698265398576758677833500000000000)
      constant := (822768865621106414036591170955790183039352365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109619936556447222007/25000000000000000000)
  centralHi := (438479746225788888029/100000000000000000000)
  directionLo := (1765271329856731531/400000000000000000)
  directionHi := (441317832464182882751/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree079.table
  base := (29378586989773224599643256625303455647889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1093050043538247237921651534721437000000000000)
      constant := (22748189119950344835709475859523122257018798587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree079.table
  base := (29378585028832704533498787990995024453829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-20548095281275929874433899448870910750000000000)
      constant := (428102462371133371098759179505308742442027799287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1765271329856731531/400000000000000000)
  centralHi := (441317832464182882751/100000000000000000000)
  directionLo := (444137783409086867233/100000000000000000000)
  directionHi := (222068891704543433617/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree080.table
  base := (30871599623374081978377178393539532562039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1106879414407401304207218330060057000000000000)
      constant := (23338094621328878427562466463007485143583603037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree080.table
  base := (3087159794572110955756278637421640444159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-20808071836335839191789382248080237000000000000)
      constant := (439203570631263316101477000663853047320447762770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444137783409086867233/100000000000000000000)
  centralHi := (222068891704543433617/50000000000000000000)
  directionLo := (223469971166256096297/50000000000000000000)
  directionHi := (89387988466502438519/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree081.table
  base := (32394163228189077708078898376735919065871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-41507732788020569277510560199951000000000000)
      constant := (886502619059484172748505633150694301185845759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree081.table
  base := (4049270224140342080842400857815160296817/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-7022682797131916169714955015763187750000000000)
      constant := (150149046502854615935115766464873873423378392936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223469971166256096297/50000000000000000000)
  centralHi := (89387988466502438519/20000000000000000000)
  directionLo := (449724641811899930061/100000000000000000000)
  directionHi := (224862320905949965031/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree082.table
  base := (6789255470412885704364461708456782123103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1134538156145709436778351920737297000000000000)
      constant := (24540617393323815059249527154677155095321400745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree082.table
  base := (8486569031173518560981460919703215505113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-21328024946455657826500347846498889500000000000)
      constant := (461833168883324297380220592801579769251221287756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449724641811899930061/100000000000000000000)
  centralHi := (224862320905949965031/50000000000000000000)
  directionLo := (226246102095425092299/50000000000000000000)
  directionHi := (452492204190850184599/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree083.table
  base := (35527941613011589522290292509790990664219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1148367527014863503063918716075917000000000000)
      constant := (25153234652026163225913711268571565719657039977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree083.table
  base := (35527940563433664212402339423669236295553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-21588001501515567143855830645708215750000000000)
      constant := (473361658654431742749454070869130340518113701259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226246102095425092299/50000000000000000000)
  centralHi := (452492204190850184599/100000000000000000000)
  directionLo := (7113170968978776541/1562500000000000000)
  directionHi := (3641943536117133589/800000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree084.table
  base := (742783113766490909179240903383109873907/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-129132988653779729927720612379393000000000000)
      constant := (2863713609567100794264335086373821768494520450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree084.table
  base := (18569577395457481931739739388273875377059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-7282659352191825487070437814972514000000000000)
      constant := (161677536245494409961437739993552610840168903318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7113170968978776541/1562500000000000000)
  centralHi := (3641943536117133589/800000000000000000)
  directionLo := (457977158442207454233/100000000000000000000)
  directionHi := (228988579221103727117/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree085.table
  base := (7755983861076963296658409363075884456079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1176026268753171635635052306753157000000000000)
      constant := (26401180891663237078968665023109159288430881785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree085.table
  base := (3877991853819087639935996332148358267007/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-22107954611635385778566796244126868250000000000)
      constant := (496846019057346340582338411309105231908798284210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457977158442207454233/100000000000000000000)
  centralHi := (228988579221103727117/50000000000000000000)
  directionLo := (230347573818051726523/50000000000000000000)
  directionHi := (460695147636103453047/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree086.table
  base := (40450232233892453521788624264111927349061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1189855639622325701920619102091777000000000000)
      constant := (27036509865414778845065977437713772658326638263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree086.table
  base := (20225115789055211002655227830168099553/5000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-22367931166695295095922279043336194500000000000)
      constant := (508801889556098500604278719564279053327576518000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230347573818051726523/50000000000000000000)
  centralHi := (460695147636103453047/100000000000000000000)
  directionLo := (463397195131890632783/100000000000000000000)
  directionHi := (28962324695743164549/6250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree087.table
  base := (21075047139650942622374146822328636869713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-133742778943497752022909544158933000000000000)
      constant := (3075489933842204227929866462339232093424469062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree087.table
  base := (21075046859414156581698843747247668413123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-7542635907251734804425920614181840250000000000)
      constant := (173633406727095409433987296129562376115415718646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463397195131890632783/100000000000000000000)
  centralHi := (28962324695743164549/6250000000000000000)
  directionLo := (466083578188242854259/100000000000000000000)
  directionHi := (23304178909412142713/5000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree088.table
  base := (43879505277275771500029284217723678586973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1217514381360633834491752692769017000000000000)
      constant := (28329879506811184468484086281657803301257735359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree088.table
  base := (10969876199580558489318845512795436588433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-22887884276815113730633244641754847000000000000)
      constant := (533141010889454652479676097313039743917309983596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466083578188242854259/100000000000000000000)
  centralHi := (23304178909412142713/5000000000000000000)
  directionLo := (468754566118996068261/100000000000000000000)
  directionHi := (234377283059498034131/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree089.table
  base := (22819232544499496524378630270175012227701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1231343752229787900777319488107637000000000000)
      constant := (28987920170126121748322999666396102399296506766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree089.table
  base := (45638464679761375287901880755903370192629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-23147860831875023047988727440964173250000000000)
      constant := (545524261643905339644631076382682406744211175687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468754566118996068261/100000000000000000000)
  centralHi := (234377283059498034131/50000000000000000000)
  directionLo := (471410420608264262449/100000000000000000000)
  directionHi := (9428208412165285249/2000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree090.table
  base := (11856743399304847287689394535947032082227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-46117523077738591372699491979491000000000000)
      constant := (1098278940475923602927171254382253919885992332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree090.table
  base := (47426973247594066358147668922655309216663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-7802612462311644121781403413391166500000000000)
      constant := (186016657471215661678008099456761514955528888863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471410420608264262449/100000000000000000000)
  centralHi := (9428208412165285249/2000000000000000000)
  directionLo := (1481410612530205631/312500000000000000)
  directionHi := (474051396009665801921/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree091.table
  base := (49245030702902539785691276381148030948039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1259002493968096033348453078784877000000000000)
      constant := (30326713173568122439465457512512534326030841037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree091.table
  base := (49245030404242860489954395757060299746473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-140046236343164743684613568280371750000000000)
      constant := (3377030432973426181754204020223324219135152651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1481410612530205631/312500000000000000)
  centralHi := (474051396009665801921/100000000000000000000)
  directionLo := (119169434907657151193/25000000000000000000)
  directionHi := (476677739630628604773/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree092.table
  base := (25546318161202683396437644617407227453363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (2646)
      previous := (1323)
      next := (1323)
      square := (25287350228034660010179024390000000000000)
      linear := (-2406109385325614555073761576793000000000000)
      constant := (58615246712827983259450783302535990282481602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree092.table
  base := (51092636067312765707794171274126864132843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (49686)
      previous := (24843)
      next := (24843)
      square := (474840243170873060191139457990000000000000)
      linear := (-45232118141880436673072166046488000000000000)
      constant := (1103078967671820178939748795552758945115351401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119169434907657151193/25000000000000000000)
  centralHi := (476677739630628604773/100000000000000000000)
  directionLo := (239644846001336800549/50000000000000000000)
  directionHi := (479289692002673601099/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree093.table
  base := (26484895192544047701879994360765372816271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-142962359522933796213287407718013000000000000)
      constant := (3521754267154959054485161121713668293318844154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree093.table
  base := (1324244754180823801805035466746775314101/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-8062589017371553439136886212600492750000000000)
      constant := (198827288190879809853256570854576231214550240040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239644846001336800549/50000000000000000000)
  centralHi := (479289692002673601099/100000000000000000000)
  directionLo := (24094374356925627041/5000000000000000000)
  directionHi := (481887487138512540821/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree094.table
  base := (54876492831296594822404319750941554083729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1300490606575558232205153464800737000000000000)
      constant := (32391681852641967527657988607801416216977901307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree094.table
  base := (54876492645264636220487858998764625774571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-24447743607174569634766141437010804500000000000)
      constant := (609577415179494771504165194088671949895367265913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24094374356925627041/5000000000000000000)
  centralHi := (481887487138512540821/100000000000000000000)
  directionLo := (242235676388368965621/50000000000000000000)
  directionHi := (484471352776737931243/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree095.table
  base := (14203185902664414700190711212771384922471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1314319977444712298490720260139357000000000000)
      constant := (33095145855108530751283246920764719763390613172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree095.table
  base := (56812743451818291858262762258686749103401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-24707720162234478952121624236220130750000000000)
      constant := (622815425705658840771579080463480404318216958403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242235676388368965621/50000000000000000000)
  centralHi := (484471352776737931243/100000000000000000000)
  directionLo := (487041510614829239273/100000000000000000000)
  directionHi := (243520755307414619637/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree096.table
  base := (1469463567015967365184764526742323022401/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-147572149812651818308476339497553000000000000)
      constant := (3756242267909647571028777371422850665462015480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree096.table
  base := (58778542545032161149722820071613502474697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-8322565572431462756492369011809819000000000000)
      constant := (212065298713301396108391805657080972734740386497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487041510614829239273/100000000000000000000)
  centralHi := (243520755307414619637/50000000000000000000)
  directionLo := (122399544132787517989/25000000000000000000)
  directionHi := (489598176531150071957/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree097.table
  base := (15193472501332703730189945399778797196441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1341978719183020431061853850816597000000000000)
      constant := (34524785520363973053971856066270581241427067212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree097.table
  base := (3798368118098218618846784495405691621023/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-25227673272354297586832589834638783250000000000)
      constant := (649718826472753929231667338980453323880769206704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122399544132787517989/25000000000000000000)
  centralHi := (489598176531150071957/100000000000000000000)
  directionLo := (15379423774892671221/3125000000000000000)
  directionHi := (492141560796565479073/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree098.table
  base := (31399392777210343099008614554941884966933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1355808090052174497347420646155217000000000000)
      constant := (35250961182207000152429253588042695885965408078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree098.table
  base := (62798785455614271854219254628258236886609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-25487649827414206904188072633848109500000000000)
      constant := (663384216696209705509360615332086621626449193627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15379423774892671221/3125000000000000000)
  centralHi := (492141560796565479073/100000000000000000000)
  directionLo := (247335934138133233269/50000000000000000000)
  directionHi := (494671868276266466539/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree099.table
  base := (12970645860464371993056913743786486600991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-50727313367456613467888423759031000000000000)
      constant := (1332766940605572525595510532049154257059621195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree099.table
  base := (64853229217994383989487991035914894755507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-8582542127491372073847851811019145250000000000)
      constant := (225730688934507297967754787581371718701349581307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247335934138133233269/50000000000000000000)
  centralHi := (494671868276266466539/100000000000000000000)
  directionLo := (497189298622349964961/100000000000000000000)
  directionHi := (248594649311174982481/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree100.table
  base := (16734305306860213292154024770466465113681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1383466831790482629918554236832457000000000000)
      constant := (36726024162485927451460941945821990084874822892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree100.table
  base := (13387444231095587467784684829567100456299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-26007602937534025538899038232266762000000000000)
      constant := (691142376788995499544754391338691953343403803485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497189298622349964961/100000000000000000000)
  centralHi := (248594649311174982481/50000000000000000000)
  directionLo := (499694046457666588957/100000000000000000000)
  directionHi := (249847023228833294479/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree101.table
  base := (69050761311557079423437539283668511341921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1397296202659636696204121032171077000000000000)
      constant := (37474911480353163298244851875218004347496657643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree101.table
  base := (69050761250151904573712643597361544792601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-26267579492593934856254521031476088250000000000)
      constant := (705235146647826194765161092116748099733947466003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499694046457666588957/100000000000000000000)
  centralHi := (249847023228833294479/50000000000000000000)
  directionLo := (502186301551415300921/100000000000000000000)
  directionHi := (251093150775707650461/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree102.table
  base := (71193849539298973875939506306768939989401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-156791730392087862498854203056633000000000000)
      constant := (4247929927748068185624839415097248307763179387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree102.table
  base := (71193849486907740999592576472933494369949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-8842518682551281391203334610228471500000000000)
      constant := (239823458791987274183949675378061531736417810549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502186301551415300921/100000000000000000000)
  centralHi := (251093150775707650461/50000000000000000000)
  directionLo := (252333124493466666039/50000000000000000000)
  directionHi := (504666248986933332079/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree103.table
  base := (36683242948850696342087237272165744712823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1424954944397944828775254622848317000000000000)
      constant := (38995397770439097419102514019551247663466501818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree103.table
  base := (14673297170601040196847689896984967591661/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-26787532602713753490965486629894740750000000000)
      constant := (733848065969985410805491792220403740088368775915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252333124493466666039/50000000000000000000)
  centralHi := (504666248986933332079/100000000000000000000)
  directionLo := (50713406932210120937/10000000000000000000)
  directionHi := (507134069322101209371/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree104.table
  base := (37784335187915840888474415119830180352731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1438784315267098895060821418186937000000000000)
      constant := (39766996742316463445582871340959156931956113746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree104.table
  base := (15113734067540780922430503212863604253123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-160044432886234691173496860527243000000000000)
      constant := (4428214292467552410719604427528729699748531005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50713406932210120937/10000000000000000000)
  centralHi := (507134069322101209371/100000000000000000000)
  directionLo := (509589938742756303187/100000000000000000000)
  directionHi := (127397484685689075797/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree105.table
  base := (77800402964473764406418300188159357739357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-161401520681805884594043134836173000000000000)
      constant := (4505129585025897613986129660657523900732359559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree105.table
  base := (2431262591623504212412046788914826089349/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-9102495237611190708558817409437797750000000000)
      constant := (254343608248208988230852199721188173383656978368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509589938742756303187/100000000000000000000)
  centralHi := (127397484685689075797/25000000000000000000)
  directionLo := (512034029209483779291/100000000000000000000)
  directionHi := (128008507302370944823/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree106.table
  base := (40030841827930624357587389476887178248871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1466443057005407027631955008864177000000000000)
      constant := (41332906339078015285080040864483761133857248986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree106.table
  base := (80061683628123978350239202137524584850241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-27567462267893481443031935027522719500000000000)
      constant := (777835893920771939853266442862688393699339186923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512034029209483779291/100000000000000000000)
  centralHi := (128008507302370944823/25000000000000000000)
  directionLo := (514466508598131054899/100000000000000000000)
  directionHi := (5144665085981310549/1000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree107.table
  base := (8235251244345195210190732640100686500149/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1480272427874561093917521804202797000000000000)
      constant := (42127216963757831729102968938701970052816281670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree107.table
  base := (82352512419797304200150165672415839480117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-27827438822953390760387417826732045750000000000)
      constant := (792783422953728848074063424527919098107023319751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514466508598131054899/100000000000000000000)
  centralHi := (5144665085981310549/1000000000000000000)
  directionLo := (516887540834370683897/100000000000000000000)
  directionHi := (258443770417185341949/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree108.table
  base := (21168222330434354578138358381325767379087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-55337103657174635563077355538571000000000000)
      constant := (1589966597747920391750636161202233323774148092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree108.table
  base := (42336444650783118732641450393581692432359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-9362471792671100025914300208647124000000000000)
      constant := (269291137280682605831356087207518852645290653918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516887540834370683897/100000000000000000000)
  centralHi := (258443770417185341949/50000000000000000000)
  directionLo := (64912160752827112761/12500000000000000000)
  directionHi := (519297286022616902089/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree109.table
  base := (43511407143040999733821844595863348209557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1507931169612869226488655394880037000000000000)
      constant := (43738549865319860870910201506518455404954205262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree109.table
  base := (10877851783610346578313379737257103873567/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-28347391933073209395098383425150698250000000000)
      constant := (823105860584509059389033631633140895452555820808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64912160752827112761/12500000000000000000)
  centralHi := (519297286022616902089/100000000000000000000)
  directionLo := (5216959005695827339/1000000000000000000)
  directionHi := (521695900569582733901/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree110.table
  base := (4470114366629345850909857267671271373471/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1521760540482023292774222190218657000000000000)
      constant := (44555572142080176356016949519923245380545725860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree110.table
  base := (11175285914740375093853519711387646156443/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-28607368488133118712453866224360024500000000000)
      constant := (838480769180086989911403632316400707365521855432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5216959005695827339/1000000000000000000)
  centralHi := (521695900569582733901/100000000000000000000)
  directionLo := (524083537302747490959/100000000000000000000)
  directionHi := (6551044216284343637/1250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree111.table
  base := (45905654228987713430768776604511901692981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-170621101261241928784420998395253000000000000)
      constant := (5042240552158666144063210614560513775973521694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree111.table
  base := (45905654222737064144805889724067963061889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-9622448347731009343269783007856450250000000000)
      constant := (284666045875973309397684616680094400064204376978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524083537302747490959/100000000000000000000)
  centralHi := (6551044216284343637/1250000000000000000)
  directionLo := (131615086395997145821/25000000000000000000)
  directionHi := (105292069116797716657/20000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree112.table
  base := (47124938829747907394382737665392543842819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1549419282220331425345355780895897000000000000)
      constant := (46212328347324014958520328875102227407413967554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree112.table
  base := (11781234706104882309070860461605921576843/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-29127321598252937347164831822778677000000000000)
      constant := (869657965927284504788901922508182602877392185032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131615086395997145821/25000000000000000000)
  centralHi := (105292069116797716657/20000000000000000000)
  directionLo := (264413235709308363453/50000000000000000000)
  directionHi := (528826471418616726907/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree113.table
  base := (4835899746741972809100421082958901376801/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1563248653089485491630922576234517000000000000)
      constant := (47052062275735261256454176776575770767296973660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree113.table
  base := (96717994925755807672736092832111701962287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-29387298153312846664520314621988003250000000000)
      constant := (885460254077574048904247000177490331074828760261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264413235709308363453/50000000000000000000)
  centralHi := (528826471418616726907/100000000000000000000)
  directionLo := (53118205756003978613/10000000000000000000)
  directionHi := (531182057560039786131/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree114.table
  base := (2480391507051790072103854991605064515911/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-175230891550959950879609930174793000000000000)
      constant := (5322151861626011131382489532173251495470030280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree114.table
  base := (19843132054865890526788873956010644192629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-9882424902790918660625265807065776500000000000)
      constant := (300468334026093445479004389858887755413576126145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53118205756003978613/10000000000000000000)
  centralHi := (531182057560039786131/100000000000000000000)
  directionLo := (4268217948882140481/800000000000000000)
  directionHi := (266763621805133780063/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree115.table
  base := (2543571842489323065939020027417024598487/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (2646)
      previous := (1323)
      next := (1323)
      square := (25287350228034660010179024390000000000000)
      linear := (-3007386379636660915315796156733000000000000)
      constant := (92163027947065033674572996427655386566365960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree115.table
  base := (101742873692974662214881304336307886224593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (49686)
      previous := (24843)
      next := (24843)
      square := (474840243170873060191139457990000000000000)
      linear := (-56535446622746059166788809490371750000000000)
      constant := (1734389810829826421208142825630875559253368651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4268217948882140481/800000000000000000)
  centralHi := (266763621805133780063/50000000000000000000)
  directionLo := (33491385382278608983/6250000000000000000)
  directionHi := (535862166116457743729/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree116.table
  base := (104299635185990122748619956194508060127449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1604736765696947690487622962250377000000000000)
      constant := (49616687363805840071131497821574930622800354067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree116.table
  base := (26074908795091792380384745883498267794689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-30167227818492574616586763019615982000000000000)
      constant := (933721877629312397696756551442243223794355895468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33491385382278608983/6250000000000000000)
  centralHi := (535862166116457743729/100000000000000000000)
  directionLo := (269093479331845999383/50000000000000000000)
  directionHi := (538186958663691998767/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree117.table
  base := (53442972370097124199726787454471198064619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-59946893946892657658266287318111000000000000)
      constant := (1869877907186788410837992635682547527552366902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree117.table
  base := (106885944735402795595573196927718970717567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-60014209809768212887460050924704750000000000)
      constant := (1873952672936857702092298554937097718322092943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269093479331845999383/50000000000000000000)
  centralHi := (538186958663691998767/100000000000000000000)
  directionLo := (540501751964160507219/100000000000000000000)
  directionHi := (27025087598208025361/5000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree118.table
  base := (109501802361245464662010616286778519192213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1632395507435255823058756552927617000000000000)
      constant := (51364290174696320216054672117856623589622378279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree118.table
  base := (109501802357162851484987230744266403556811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-30687180928612393251297728618034634500000000000)
      constant := (966608592577755153478231627867210424951897380633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540501751964160507219/100000000000000000000)
  centralHi := (27025087598208025361/5000000000000000000)
  directionLo := (271403336971461744257/50000000000000000000)
  directionHi := (108561334788584697703/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree119.table
  base := (5607360402418165799837861692006101753039/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1646224878304409889344323348266237000000000000)
      constant := (52249447405753792194946948755471856026773120740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree119.table
  base := (112147208044884927699097899988225425720203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-30947157483672302568653211417243960750000000000)
      constant := (983265639825412812736435630719224935877873105209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271403336971461744257/50000000000000000000)
  centralHi := (108561334788584697703/20000000000000000000)
  directionLo := (27255092491020445069/5000000000000000000)
  directionHi := (545101849820408901381/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree120.table
  base := (57411080900450806548138628707750700171341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-184450472130395995069987793733873000000000000)
      constant := (5904686131911830389713867324219160722343836334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree120.table
  base := (28705540449484558485102325463287701812967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-10402378012910737295336231405484429000000000000)
      constant := (333355048973930217628416027429585015319124251068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27255092491020445069/5000000000000000000)
  centralHi := (545101849820408901381/100000000000000000000)
  directionLo := (547387402191796871447/100000000000000000000)
  directionHi := (68423425273974608931/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree121.table
  base := (29381665904581807201564142540886442010401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1673883620042718021915456938943477000000000000)
      constant := (54042473519046749498343175074398831204938229932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree121.table
  base := (117526663615802782003120058718157529157531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-31467110593792121203364177015662613250000000000)
      constant := (1017007113866749211527908435693746530441074786793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547387402191796871447/100000000000000000000)
  centralHi := (68423425273974608931/12500000000000000000)
  directionLo := (137415862775858311963/25000000000000000000)
  directionHi := (549663451103433247853/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree122.table
  base := (60130356750101098138185339013884538177999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1687712990911872088201023734282097000000000000)
      constant := (54950342401268364687178871476142219717592719434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree122.table
  base := (24052142699610362908219814221028929792659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-31727087148852030520719659814871939500000000000)
      constant := (1034091540660174031063912291660874282254652608885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137415862775858311963/25000000000000000000)
  centralHi := (549663451103433247853/100000000000000000000)
  directionLo := (110386022825281411529/20000000000000000000)
  directionHi := (275965057063203528823/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree123.table
  base := (24604862289233719326650566926236552355757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-189060262420114017165176725513413000000000000)
      constant := (6207309092651800768740399764966676042942931795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree123.table
  base := (123024311444336975170944434634745628831827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-10662354567970646612691714204693755250000000000)
      constant := (350439475767323893755387369743293019283506665627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110386022825281411529/20000000000000000000)
  centralHi := (275965057063203528823/50000000000000000000)
  directionLo := (13854687660685486517/2500000000000000000)
  directionHi := (554187506427419460681/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree124.table
  base := (62908728727967901503426956108715562493573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1715371732650180220772157324959337000000000000)
      constant := (56788791816836125169212442608328396758191406318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree124.table
  base := (31454364363593948433837093859165667450801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-32247040258971849155430625413290592000000000000)
      constant := (1068687773792066402791057471525425376654228722412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13854687660685486517/2500000000000000000)
  centralHi := (554187506427419460681/100000000000000000000)
  directionLo := (556435740837065077717/100000000000000000000)
  directionHi := (278217870418532538859/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree125.table
  base := (128640151529269714944393538478605702928287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1729201103519334287057724120297957000000000000)
      constant := (57719372350174775782058343589353300254924723221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree125.table
  base := (32160037881985281686152962601450029460103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-32507016814031758472786108212499918250000000000)
      constant := (1086199580130397275073230626089597268966089519636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556435740837065077717/100000000000000000000)
  centralHi := (278217870418532538859/50000000000000000000)
  directionLo := (558674927915640240743/100000000000000000000)
  directionHi := (69834365989455030093/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree126.table
  base := (26298478733196734805177136289371072570577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (51842)
      previous := (25921)
      next := (25921)
      square := (495444750764086486866100144530000000000000)
      linear := (-64556684236610679753455219097651000000000000)
      constant := (2172500867921462693147727419747332486949176165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree126.table
  base := (131492393664852248928799120196266300233243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-10922331123030555930047197003903081500000000000)
      constant := (367951282105638609017702999274202850163402157443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558674927915640240743/100000000000000000000)
  centralHi := (69834365989455030093/12500000000000000000)
  directionLo := (280452588008293384737/50000000000000000000)
  directionHi := (22436207040663470779/4000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree127.table
  base := (26874836773186159893671293947399121202089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1756859845257642419628857710975197000000000000)
      constant := (59603245067948178069780117034807837240647185935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree127.table
  base := (16796772983120917383179453783451520854081/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-33026969924151577107497073810918570750000000000)
      constant := (1121650572351584021853361243773047164629454191544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280452588008293384737/50000000000000000000)
  centralHi := (22436207040663470779/4000000000000000000)
  directionLo := (281563295673837143101/50000000000000000000)
  directionHi := (563126591347674286203/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree128.table
  base := (27457104425799504607627306264295872697271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (1399734)
      previous := (699867)
      next := (699867)
      square := (13377008270630335145384703902310000000000000)
      linear := (-1770689216126796485914424506313817000000000000)
      constant := (60556537252379209751351274053573425748675608465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree128.table
  base := (68642761064088571572915058362120451723167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (26283894)
      previous := (13141947)
      next := (13141947)
      square := (251190488637391848841112773276710000000000000)
      linear := (-33286946479211486424852556610127897000000000000)
      constant := (1139589758234372557221094340890322359027017117802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell092.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281563295673837143101/50000000000000000000)
  centralHi := (563126591347674286203/100000000000000000000)
  directionLo := (565339278030018818901/100000000000000000000)
  directionHi := (282669639015009409451/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree129.table
  base := (70113204227549068417990300042542548992999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (155526)
      previous := (77763)
      next := (77763)
      square := (1486334252292259460598300433590000000000000)
      linear := (-198279842999550061355554589072493000000000000)
      constant := (6835266665241262621530799028172337050503778826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree129.table
  base := (17528301056799953955720222693603521111761/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (8761298)
      previous := (4380649)
      next := (4380649)
      square := (83730162879130616280370924425570000000000000)
      linear := (-11182307678090465247402679803112407750000000000)
      constant := (385890467988419810863941232827931231135112861288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell092.Kernel129
