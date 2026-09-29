import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell035.Parameters
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch000_049
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch050_099
import ForestUnimodality.BinomialMassData.Q9_19.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_19.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree000.table
  base := (2613681964915370944446237867/50000000000000000000000000)
  polynomial :=
    { denominator := 35720000000000000000000000000000000000000000
      center := (213005)
      previous := (190631)
      next := (0)
      square := (8898442928106320717329680398800000000000000)
      linear := (35847518536352360252195127768000000000000000)
      constant := (1867214395735541002712392332184800000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree000.table
  base := (2613681964915370944446237867/50000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (190678290086980639639335786000000000000000)
      constant := (9931991466678409588895703894600000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree001.table
  base := (156210042515893879782886466961070528922539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (1289789339110788220007508614759800000000000000)
      constant := (51747899553193797601633816950973204355263074952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree001.table
  base := (155900171089664034106907308540647796559717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (145837312285772976450104473800000000000000)
      constant := (5844505437687370597514978715644616269269246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49923125646186015803/100000000000000000000)
  directionHi := (12480781411546503951/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree002.table
  base := (24317370822041557627702279283560864508949/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (894745307013015508161846224423600000000000000)
      constant := (31441685007433417851913340505816557417763151328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree002.table
  base := (193847844571199232067348455663336269682293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (100996334484565313260873161600000000000000)
      constant := (3544947382582053115800574314003389123963567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49923125646186015803/100000000000000000000)
  centralHi := (12480781411546503951/25000000000000000000)
  directionLo := (70601961364892348123/100000000000000000000)
  directionHi := (17650490341223087031/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree003.table
  base := (1979234945242561977135287538189211381917/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (499701274915242796316183834087400000000000000)
      constant := (19718457726060378371239532690419159073072232192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree003.table
  base := (63039277851414272608500944671100048823231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (56155356683357650071641849400000000000000)
      constant := (2220110756701133574328393893401801855282778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70601961364892348123/100000000000000000000)
  centralHi := (17650490341223087031/25000000000000000000)
  directionLo := (86469390091839017747/100000000000000000000)
  directionHi := (21617347522959754437/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree004.table
  base := (43059131730055554895180688799004379140387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (104657242817470084470521443751200000000000000)
      constant := (12767581417394676353056189000871702375209462216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree004.table
  base := (21412756505968699116019067001881072949199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (11314378882149986882410537200000000000000)
      constant := (1436008018588128960323163101742961544139124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86469390091839017747/100000000000000000000)
  centralHi := (21617347522959754437/25000000000000000000)
  directionLo := (99846251292372031607/100000000000000000000)
  directionHi := (12480781411546503951/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree005.table
  base := (60701769166397407478365233212910946964773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-290386789280302627375140946585000000000000000)
      constant := (8544417276298531394293811765748216420233950332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree005.table
  base := (471410989691499619276215440006877804637/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-33526598919057676306820775000000000000000)
      constant := (960370840020344617501777647596726820877184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99846251292372031607/100000000000000000000)
  centralHi := (12480781411546503951/12500000000000000000)
  directionLo := (55815751297067522967/50000000000000000000)
  directionHi := (22326300518827009187/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree006.table
  base := (10964493722420890154727965456491274369529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-685430821378075339220803336921200000000000000)
      constant := (5947045452154526384698922871755424425016026544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree006.table
  base := (21787708414483376157353744427269289518261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-78367576720265339496052087200000000000000)
      constant := (668333484966088656933723347836233001693918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55815751297067522967/50000000000000000000)
  centralHi := (22326300518827009187/20000000000000000000)
  directionLo := (24457236839601693147/20000000000000000000)
  directionHi := (15285773024751058217/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree007.table
  base := (2001478034902758836099220847061485303347/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-1080474853475848051066465727257400000000000000)
      constant := (4377256291866686397718807691016401378673723968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree007.table
  base := (15898098729557888456639504281053036014951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-123208554521473002685283399400000000000000)
      constant := (492270032233016047454793258580015368568138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24457236839601693147/20000000000000000000)
  centralHi := (15285773024751058217/12500000000000000000)
  directionLo := (33021043782709734407/25000000000000000000)
  directionHi := (132084175130838937629/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree008.table
  base := (23242796932022670003658052318566815301847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-1475518885573620762912128117593600000000000000)
      constant := (3506669826220638986881206449608671220135281748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree008.table
  base := (11526709708102816740031566724384859541201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-168049532322680665874514711600000000000000)
      constant := (395139427880812348987854341926624662565638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33021043782709734407/25000000000000000000)
  centralHi := (132084175130838937629/100000000000000000000)
  directionLo := (141203922729784696247/100000000000000000000)
  directionHi := (17650490341223087031/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree009.table
  base := (8211758938560879821076243365636293363901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-1870562917671393474757790507929800000000000000)
      constant := (3151973157469885657426179301811441950210310968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree009.table
  base := (1626084784931867375873368224451283683957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-212890510123888329063746023800000000000000)
      constant := (356303209742042244662709153745743899951830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141203922729784696247/100000000000000000000)
  centralHi := (17650490341223087031/12500000000000000000)
  directionLo := (149769376938558047411/100000000000000000000)
  directionHi := (37442344234639511853/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree010.table
  base := (1094113446048779218881778226182792617089/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-2265606949769166186603452898266000000000000000)
      constant := (3208293023352075987539306441032219557273696760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree010.table
  base := (10797941360282024917248589460702670840267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-257731487925095992252977336000000000000000)
      constant := (363971091251421150670558449753350745965073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149769376938558047411/100000000000000000000)
  centralHi := (37442344234639511853/25000000000000000000)
  directionLo := (9866924059794570283/6250000000000000000)
  directionHi := (157870784956713124529/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree011.table
  base := (803234275413849948168856641545114451367/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-2660650981866938898449115288602200000000000000)
      constant := (3613550541034677299720432614538754956426379424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree011.table
  base := (6297675309192323055104699096109361920471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-302572465726303655442208648200000000000000)
      constant := (411169604250785152901842265926077876488949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9866924059794570283/6250000000000000000)
  centralHi := (157870784956713124529/100000000000000000000)
  directionLo := (646782328633468673/390625000000000000)
  directionHi := (165576276130167980289/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree012.table
  base := (331118974255659942859360005089642710087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-3055695013964711610294777678938400000000000000)
      constant := (4329336317274184487703761890608156613921967264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree012.table
  base := (2532982274874492010031761641241625194587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-347413443527511318631439960400000000000000)
      constant := (493584467737807804273425861583590878697153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (646782328633468673/390625000000000000)
  centralHi := (165576276130167980289/100000000000000000000)
  directionLo := (86469390091839017747/50000000000000000000)
  directionHi := (34587756036735607099/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree013.table
  base := (-538830988500705307757998095738567882843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-3450739046062484322140440069274600000000000000)
      constant := (5330602357904010338207274759243301269556785788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree013.table
  base := (-128862189265616486186314504932389629361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-392254421328718981820671272600000000000000)
      constant := (608400390843013434739043593931422985210705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86469390091839017747/50000000000000000000)
  centralHi := (34587756036735607099/20000000000000000000)
  directionLo := (180000389348754983947/100000000000000000000)
  directionHi := (45000097337188745987/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree014.table
  base := (-648083481297252174151485179528957994799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-3845783078160257033986102459610800000000000000)
      constant := (6600066136299835515608639242952902080005823420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree014.table
  base := (-3336560307136301197421914302791635623577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-437095399129926645009902584800000000000000)
      constant := (753672610464704926635599855846958923152037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180000389348754983947/100000000000000000000)
  centralHi := (45000097337188745987/25000000000000000000)
  directionLo := (186795231844895501797/100000000000000000000)
  directionHi := (93397615922447750899/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree015.table
  base := (-5530792712611550531161569185327580062979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-4240827110258029745831764849947000000000000000)
      constant := (8125138828297345790174107911157339548706833564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree015.table
  base := (-5618427151469392402071207275687538915507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-481936376931134308199133897000000000000000)
      constant := (927982561068416945823087719261936760605367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186795231844895501797/100000000000000000000)
  centralHi := (93397615922447750899/50000000000000000000)
  directionLo := (96675717109149413423/50000000000000000000)
  directionHi := (193351434218298826847/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree016.table
  base := (-3733598964446100455601000459829447279149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-4635871142355802457677427240283200000000000000)
      constant := (9896210582156469702056955368893586145974698568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree016.table
  base := (-117921565307668252110379997507401641647/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-526777354732341971388365209200000000000000)
      constant := (1130245937347244662587994684630999603757248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96675717109149413423/50000000000000000000)
  centralHi := (193351434218298826847/100000000000000000000)
  directionLo := (39938500516948812643/20000000000000000000)
  directionHi := (12480781411546503951/6250000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree017.table
  base := (-909497300415851741627971470314176700817/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-5030915174453575169523089630619400000000000000)
      constant := (11905669545907780258576841206199022587600387720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree017.table
  base := (-17905215069171047472776844288378971143/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-571618332533549634577596521400000000000000)
      constant := (1359602975552500266646771398662649368720896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39938500516948812643/20000000000000000000)
  centralHi := (12480781411546503951/6250000000000000000)
  directionLo := (25729790025025858349/12500000000000000000)
  directionHi := (205838320200206866793/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree018.table
  base := (-2612753880021581536178400367192200044559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-5425959206551347881368752020955600000000000000)
      constant := (14147321205949213071043596737679118750877027376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree018.table
  base := (-10516748097681073195648826861142018935523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-616459310334757297766827833600000000000000)
      constant := (1615353504042475888668296282038301640225063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25729790025025858349/12500000000000000000)
  centralHi := (205838320200206866793/100000000000000000000)
  directionLo := (211805884094677044371/100000000000000000000)
  directionHi := (52951471023669261093/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree019.table
  base := (-578296029172397135866941557258840185657/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-5821003238649120593214414411291800000000000000)
      constant := (16616029133375404703768930295034612485423204240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree019.table
  base := (-2906345697636686339852049878415487411291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-661300288135964960956059145800000000000000)
      constant := (1896916718200041284096499328340422956741884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211805884094677044371/100000000000000000000)
  centralHi := (52951471023669261093/25000000000000000000)
  directionLo := (217609859637408529951/100000000000000000000)
  directionHi := (6800308113669016561/3125000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree020.table
  base := (-12465376265164284561927650150773133335429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-6216047270746893305060076801628000000000000000)
      constant := (19307480712087867855308726060557603283114837764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree020.table
  base := (-1564880445740657444706545988386570644339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-706141265937172624145290458000000000000000)
      constant := (2203804899958855784485442929765241262060472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217609859637408529951/100000000000000000000)
  centralHi := (6800308113669016561/3125000000000000000)
  directionLo := (223263005188270091869/100000000000000000000)
  directionHi := (22326300518827009187/10000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree021.table
  base := (-13171126384535656065922406416086001534069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-6611091302844666016905739191964200000000000000)
      constant := (22218025502727190223881612894279292718454360004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree021.table
  base := (-413108035836728163423454733777335726103/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-750982243738380287334521770200000000000000)
      constant := (2535605241582704366490911916963379878529376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223263005188270091869/100000000000000000000)
  centralHi := (22326300518827009187/10000000000000000000)
  directionLo := (57194125550609650143/25000000000000000000)
  directionHi := (228776502202438600573/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree022.table
  base := (-3425417947793640430396205527631867313217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-7006135334942438728751401582300400000000000000)
      constant := (25344557508657026105308723831510106351951508688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree022.table
  base := (-2749021235141785245944324872000835215319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-795823221539587950523753082400000000000000)
      constant := (2891966572861957968875147681559920654544695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57194125550609650143/25000000000000000000)
  centralHi := (228776502202438600573/100000000000000000000)
  directionLo := (46832043062103224777/20000000000000000000)
  directionHi := (117080107655258061943/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree023.table
  base := (-3518201421046753323647961236850592371749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-7401179367040211440597063972636600000000000000)
      constant := (28684425304438661820321150182349575601045163536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree023.table
  base := (-2822352731371240562302495033797183671159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-840664199340795613712984394600000000000000)
      constant := (3272589206718145294824559339689267551239895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46832043062103224777/20000000000000000000)
  centralHi := (117080107655258061943/50000000000000000000)
  directionLo := (239422899716280576281/100000000000000000000)
  directionHi := (119711449858140288141/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree024.table
  base := (-3574509406036030898493136297270321557839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-7796223399137984152442726362972800000000000000)
      constant := (32235360851005176666087855514869877342335029296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree024.table
  base := (-7166458504669900172811372494473672934239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-885505177142003276902215706800000000000000)
      constant := (3677216882187935626295853710810000428498918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239422899716280576281/100000000000000000000)
  centralHi := (119711449858140288141/50000000000000000000)
  directionLo := (24457236839601693147/10000000000000000000)
  directionHi := (244572368396016931471/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree025.table
  base := (-14388938588840167577418309035087027580641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-8191267431235756864288388753309000000000000000)
      constant := (35995421566320556585611779148350324461651666356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree025.table
  base := (-14420113570840409599109227449884443283313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-930346154943210940091447019000000000000000)
      constant := (4105630199855395838714951715952195577617053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24457236839601693147/10000000000000000000)
  centralHi := (244572368396016931471/100000000000000000000)
  directionLo := (249615628230930079019/100000000000000000000)
  directionHi := (12480781411546503951/5000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree026.table
  base := (-2871085417526024715828526124802090276351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-8586311463333529576134051143645200000000000000)
      constant := (39962942291360250396231822832827729380225443580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree026.table
  base := (-14383247290830504867031493979658301760157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-975187132744418603280678331200000000000000)
      constant := (4557641174680548920475721497986492266557017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249615628230930079019/100000000000000000000)
  centralHi := (12480781411546503951/5000000000000000000)
  directionLo := (127279495924723450081/50000000000000000000)
  directionHi := (254558991849446900163/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree027.table
  base := (-3551502346413900152829108680998717996397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-8981355495431302287979713533981400000000000000)
      constant := (44136494960307224210548683034527119911571544208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree027.table
  base := (-2846159905114847548959380797233302665493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1020028110545626266469909643400000000000000)
      constant := (5033088660894375991265423228162836246778165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127279495924723450081/50000000000000000000)
  centralHi := (254558991849446900163/100000000000000000000)
  directionLo := (129704085137758526621/50000000000000000000)
  directionHi := (259408170275517053243/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree028.table
  base := (-13947982842395697728668713044498433415531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-9376399527529074999825375924317600000000000000)
      constant := (48514854463262688962858237709297825004466993596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree028.table
  base := (-6985021438030432303778781704597876994789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1064869088346833929659140955600000000000000)
      constant := (5531834479078081179956166893625280674198018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129704085137758526621/50000000000000000000)
  centralHi := (259408170275517053243/100000000000000000000)
  directionLo := (33021043782709734407/12500000000000000000)
  directionHi := (264168350261677875257/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree029.table
  base := (-1698451115384107675230686402791932954587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-9771443559626847711671038314653800000000000000)
      constant := (53096969600399239449882549489128908022816928736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree029.table
  base := (-13607214605122062885294797757372784875289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1109710066148041592848372267800000000000000)
      constant := (6053760121237862615378307309709917087369509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33021043782709734407/12500000000000000000)
  centralHi := (264168350261677875257/100000000000000000000)
  directionLo := (134422129645997463867/50000000000000000000)
  directionHi := (53768851858398985547/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree030.table
  base := (-6565130444600606739204945678294341821597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-10166487591724620423516700704990000000000000000)
      constant := (57881938287080838839365331183537965435246018504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree030.table
  base := (-3286916159693859924578819136852745159047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1154551043949249256037603580000000000000000)
      constant := (6598763938779385762246017755599191367912428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134422129645997463867/50000000000000000000)
  centralHi := (53768851858398985547/20000000000000000000)
  directionLo := (6836005514395188307/2500000000000000000)
  directionHi := (273440220575807532281/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree031.table
  base := (-1258055013355102659132641581338715743239/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-10561531623822393135362363095326200000000000000)
      constant := (62868986344243642680593970277289785461620637240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree031.table
  base := (-6297991062856253730035848546372844298459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1199392021750456919226834892200000000000000)
      constant := (7166758737877511884703696982337831916658558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6836005514395188307/2500000000000000000)
  centralHi := (273440220575807532281/100000000000000000000)
  directionLo := (138980099926960004361/50000000000000000000)
  directionHi := (277960199853920008723/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree032.table
  base := (-119424343863805188983381425661763811047/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-10956575655920165847208025485662400000000000000)
      constant := (68057449332300980276373927867890444434618545200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree032.table
  base := (-11956103794267480382981547583251612978837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1244232999551664582416066204400000000000000)
      constant := (7757669720693890912715412714318219353402097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138980099926960004361/50000000000000000000)
  centralHi := (277960199853920008723/100000000000000000000)
  directionLo := (56481569091913878499/20000000000000000000)
  directionHi := (17650490341223087031/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree033.table
  base := (-5609655234281724635064871672539277765881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-11351619688017938559053687875998600000000000000)
      constant := (73446756979377281492459178526600106783105668392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree033.table
  base := (-2807851698918064742064597170033063735939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1289073977352872245605297516600000000000000)
      constant := (8371432721355116736758107298977487156068636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56481569091913878499/20000000000000000000)
  centralHi := (17650490341223087031/6250000000000000000)
  directionLo := (286786522785504871141/100000000000000000000)
  directionHi := (143393261392752435571/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree034.table
  base := (-5207046919041885329060117082846584710149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-11746663720115711270899350266334800000000000000)
      constant := (79036419826724368371553692168655867945042690568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree034.table
  base := (-10424788292409122094869033207179648008439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1333914955154079908794528828800000000000000)
      constant := (9007992693774026058131411292663586687839659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286786522785504871141/100000000000000000000)
  centralHi := (143393261392752435571/50000000000000000000)
  directionLo := (36387418010403545543/12500000000000000000)
  directionHi := (58219868816645672869/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree035.table
  base := (-148895106741008967379988474278631779779/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-12141707752213483982745012656671000000000000000)
      constant := (84826017772084113689394449162411070666149271296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree035.table
  base := (-9538733704047818007622902340668490638869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1378755932955287571983760141000000000000000)
      constant := (9667302414978793660183945693027298677861489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36387418010403545543/12500000000000000000)
  centralHi := (58219868816645672869/20000000000000000000)
  directionLo := (73837298586135760841/25000000000000000000)
  directionHi := (59069838868908608673/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree036.table
  base := (-8567037217770735496158195743403902815181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-12536751784311256694590675047007200000000000000)
      constant := (90815190239374683645794737750437979179776152996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree036.table
  base := (-8575375237687028945462352801034741910623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1423596910756495235172991453200000000000000)
      constant := (10349321373034544580375805722380339903698163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73837298586135760841/25000000000000000000)
  centralHi := (59069838868908608673/20000000000000000000)
  directionLo := (299538753877116094823/100000000000000000000)
  directionHi := (37442344234639511853/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree037.table
  base := (-188229711178879382409254972226506717913/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-12931795816409029406436337437343400000000000000)
      constant := (97003627742830751518490247334643280846795756320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree037.table
  base := (-7536542091726087179521427936017394606651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1468437888557702898362222765400000000000000)
      constant := (11054014813171691505555444557115669502473631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299538753877116094823/100000000000000000000)
  centralHi := (37442344234639511853/12500000000000000000)
  directionLo := (151835259037995196673/50000000000000000000)
  directionHi := (303670518075990393347/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree038.table
  base := (-3208661386985665460864268636251142185323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-13326839848506802118281999827679600000000000000)
      constant := (103391064647255729427969687012897126490718466936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree038.table
  base := (-1605950880134898547913074083443394708347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1513278866358910561551454077600000000000000)
      constant := (11781352919557117007567670994058302002165628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151835259037995196673/50000000000000000000)
  centralHi := (303670518075990393347/100000000000000000000)
  directionLo := (38468351850666088349/12500000000000000000)
  directionHi := (307746814805328706793/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree039.table
  base := (-1308199566935868507980164868413775103183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-13721883880604574830127662218015800000000000000)
      constant := (109977272954505604550918089167807362122308900912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree039.table
  base := (-209540231073819600926870797240605167651/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1558119844160118224740685389800000000000000)
      constant := (12531310113389180225627465606410712545365775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38468351850666088349/12500000000000000000)
  centralHi := (307746814805328706793/100000000000000000000)
  directionLo := (155884909867111704359/50000000000000000000)
  directionHi := (311769819734223408719/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree040.table
  base := (-3976780578536815593903767023547385554621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-14116927912702347541973324608352000000000000000)
      constant := (116762056970584829009358810977538770723548008036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree040.table
  base := (-3981803802992489774778196361015483542033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1602960821961325887929916702000000000000000)
      constant := (13303864450763255572821559789140705812701373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155884909867111704359/50000000000000000000)
  centralHi := (311769819734223408719/100000000000000000000)
  directionLo := (315741569913426249057/100000000000000000000)
  directionHi := (157870784956713124529/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree041.table
  base := (-1325135100443793456651146485591769591131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-14511971944800120253818986998688200000000000000)
      constant := (123745248728468682146778400124092297707925126392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree041.table
  base := (-663672104504314464449124356644802677393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1647801799762533551119148014200000000000000)
      constant := (14098997106117646425334780027994994996518132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315741569913426249057/100000000000000000000)
  centralHi := (157870784956713124529/50000000000000000000)
  directionLo := (63932795166699824753/20000000000000000000)
  directionHi := (159831987916749561883/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree042.table
  base := (-1254125874413646482825976929185374752549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-14907015976897892965664649389024400000000000000)
      constant := (130926704059515159407986774682342542545043063684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree042.table
  base := (-1258009640887929638506691917864145987747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1692642777563741214308379326400000000000000)
      constant := (14916691929091958211207805965960581226232807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63932795166699824753/20000000000000000000)
  centralHi := (159831987916749561883/50000000000000000000)
  directionLo := (64707766433393383731/20000000000000000000)
  directionHi := (631911781576107263/195312500000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree043.table
  base := (210915331323527567310745102400233123569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-15302060008995665677510311779360600000000000000)
      constant := (138306299221538001598571014278857635737717257996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree043.table
  base := (25937912602054403435307034235010537297/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1737483755364948877497610638600000000000000)
      constant := (15756935064362188796984071089103721601669144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64707766433393383731/20000000000000000000)
  centralHi := (631911781576107263/195312500000000000)
  directionLo := (163683913682934695107/50000000000000000000)
  directionHi := (65473565473173878043/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree044.table
  base := (1744220777808683359523993337591180938229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-15697104041093438389355974169696800000000000000)
      constant := (145883928004652714172314826839647757820633637436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree044.table
  base := (1741224805677253557002455503810822734849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1782324733166156540686841950800000000000000)
      constant := (16619714625501385102183374056172405631962131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163683913682934695107/50000000000000000000)
  centralHi := (65473565473173878043/20000000000000000000)
  directionLo := (331152552260335960577/100000000000000000000)
  directionHi := (165576276130167980289/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree045.table
  base := (836311865285935005897527917911666358683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-16092148073191211101201636560033000000000000000)
      constant := (153659499247192871720401584083224603779844547088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree045.table
  base := (3342618172538256581438844717176488964209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1827165710967364203876073263000000000000000)
      constant := (17505020415187578020202040107126353290319971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331152552260335960577/100000000000000000000)
  centralHi := (165576276130167980289/50000000000000000000)
  directionLo := (83723626945601284451/25000000000000000000)
  directionHi := (66978901556481027561/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree046.table
  base := (501352931209244470287566587153780943957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-16487192105288983813047298950369200000000000000)
      constant := (161632934703590815168248238536810353599952769880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree046.table
  base := (2505611483634451696987015808812417307129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1872006688768571867065304575200000000000000)
      constant := (18412843685172287273810534988334871857670902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83723626945601284451/25000000000000000000)
  centralHi := (66978901556481027561/20000000000000000000)
  directionLo := (84648777980364360407/25000000000000000000)
  directionHi := (338595111921457441629/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree047.table
  base := (6748666295543400899973256918144692637039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35720000000000000000000000000000000000000000
      center := (213005)
      previous := (190631)
      next := (0)
      square := (8898442928106320717329680398800000000000000)
      linear := (-359196513561420351593467262568200000000000000)
      constant := (3612854621581955379282639285605937842099503308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree047.table
  base := (6746644184796645301837630963403722127359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1916847666569779530254535887400000000000000)
      constant := (19343176930359134437846221380204670720419821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84648777980364360407/25000000000000000000)
  centralHi := (338595111921457441629/100000000000000000000)
  directionLo := (17112785300133725397/5000000000000000000)
  directionHi := (342255706002674507941/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree048.table
  base := (8550315054431787432354868739493459583727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-17277280169484529236738623731041600000000000000)
      constant := (178173139135318664255101474293003519968754423668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree048.table
  base := (2137135737820773145766838531017046458027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-1961688644370987193443767199600000000000000)
      constant := (20296013712145190107591815798757295530810052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17112785300133725397/5000000000000000000)
  centralHi := (342255706002674507941/100000000000000000000)
  directionLo := (345877560367356070989/100000000000000000000)
  directionHi := (34587756036735607099/10000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree049.table
  base := (651136304955499683774779162520900175739/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-17672324201582301948584286121377800000000000000)
      constant := (186739800989486503556969400697891015881660260416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree049.table
  base := (10416628547577280181962803814488774949863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2006529622172194856632998511800000000000000)
      constant := (21271348506866585946989010695575286724047397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345877560367356070989/100000000000000000000)
  centralHi := (34587756036735607099/10000000000000000000)
  directionLo := (349461879523302110627/100000000000000000000)
  directionHi := (87365469880825527657/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree050.table
  base := (6176005407794354127529859985103432714667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-18067368233680074660429948511714000000000000000)
      constant := (195504110309838228488048994555365709395738309256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree050.table
  base := (12350651566183230394537541745108600662429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2051370599973402519822229824000000000000000)
      constant := (22269176575780898379662063743157063412586151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349461879523302110627/100000000000000000000)
  centralHi := (87365469880825527657/25000000000000000000)
  directionLo := (353009806824461740619/100000000000000000000)
  directionHi := (17650490341223087031/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree051.table
  base := (7175793873849512346968056837775418589167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-18462412265777847372275610902050200000000000000)
      constant := (204466030646132589046406784704029651748847425256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree051.table
  base := (3587599510165521912828608709621421584917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2096211577774610183011461136200000000000000)
      constant := (23289493853525789149790909413031228040453692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353009806824461740619/100000000000000000000)
  centralHi := (17650490341223087031/5000000000000000000)
  directionLo := (71304485746277890339/20000000000000000000)
  directionHi := (22282651795711840731/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree052.table
  base := (8208362660518036033677223786234487514989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-18857456297875620084121273292386400000000000000)
      constant := (213625530712416794317352011378924781403932826552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree052.table
  base := (131325475274239255523706219854199088087/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2141052555575817846200692448400000000000000)
      constant := (24332296852428313302150773798553722834206625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71304485746277890339/20000000000000000000)
  centralHi := (22282651795711840731/6250000000000000000)
  directionLo := (72000155739501993579/20000000000000000000)
  directionHi := (45000097337188745987/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree053.table
  base := (18547263583689837646201644379947892952661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-19252500329973392795966935682722600000000000000)
      constant := (222982583655324383723870254713805447060464539324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree053.table
  base := (4636588298587458842589775853638916343759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2185893533377025509389923760600000000000000)
      constant := (25397582580412420631800782540776557642125684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72000155739501993579/20000000000000000000)
  centralHi := (45000097337188745987/12500000000000000000)
  directionLo := (363445840720592677681/100000000000000000000)
  directionHi := (181722920360296338841/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree054.table
  base := (10371532622782124954993199419738028729131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-19647544362071165507812598073058800000000000000)
      constant := (232537166426044868394815352416651698430322857608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree054.table
  base := (2592783661945542710444149419636464789619/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2230734511178233172579155072800000000000000)
      constant := (26485348470572268044849410011384742648022088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363445840720592677681/100000000000000000000)
  centralHi := (181722920360296338841/50000000000000000000)
  directionLo := (73371710518805079441/20000000000000000000)
  directionHi := (183429276297012698603/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree055.table
  base := (23004012467544625586046714929564892547099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-20042588394168938219658260463395000000000000000)
      constant := (242289259241276318843639717947391947420377168516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree055.table
  base := (23003316810065961582091579627045361520503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2275575488979440835768386385000000000000000)
      constant := (27595592320753563719635530710413861868889557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73371710518805079441/20000000000000000000)
  centralHi := (183429276297012698603/50000000000000000000)
  directionLo := (370239808888331421133/100000000000000000000)
  directionHi := (185119904444165710567/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree056.table
  base := (1013200164223770205961693377827686013881/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-20437632426266710931503922853731200000000000000)
      constant := (252238845120553276128391127397618180968859945100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree056.table
  base := (12664698152201992028086659647143384435247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2320416466780648498957617697200000000000000)
      constant := (28728312241720744146972926836191448608539386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370239808888331421133/100000000000000000000)
  centralHi := (185119904444165710567/50000000000000000000)
  directionLo := (74718092737958200719/20000000000000000000)
  directionHi := (93397615922447750899/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree057.table
  base := (27720953345323115251047246516127571216833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-20832676458364483643349585244067400000000000000)
      constant := (262385909489128685569326370358140836166166791372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree057.table
  base := (27720422474161485886304644396628632100761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2365257444581856162146849009400000000000000)
      constant := (29883506612689887785691216759435944009914459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74718092737958200719/20000000000000000000)
  centralHi := (93397615922447750899/25000000000000000000)
  directionLo := (75382266623984695937/20000000000000000000)
  directionHi := (188455666559961739843/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree058.table
  base := (754419641792608464472623925138162263249/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-21227720490462256355195247634403600000000000000)
      constant := (272730439837121776574443481967541709336131804640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree058.table
  base := (7544080534040630668067069286615637173071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2410098422383063825336080321600000000000000)
      constant := (31061174043180651692186272202182788425153396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75382266623984695937/20000000000000000000)
  centralHi := (188455666559961739843/50000000000000000000)
  directionLo := (190101598828444103439/50000000000000000000)
  directionHi := (380203197656888206879/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree059.table
  base := (32697437126452746302076471590995952349607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-21622764522560029067040910024739800000000000000)
      constant := (283272425426959800180956253702916239464261421588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree059.table
  base := (1307881300239916523644497577175964475567/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2454939400184271488525311633800000000000000)
      constant := (32261313340289261421322009380258583125894325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190101598828444103439/50000000000000000000)
  centralHi := (380203197656888206879/100000000000000000000)
  directionLo := (383466804277511977159/100000000000000000000)
  directionHi := (9586670106937799429/2500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree060.table
  base := (35282852812307794253314960529517212279517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-22017808554657801778886572415076000000000000000)
      constant := (294011857042271067191890618799687467666334432028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree060.table
  base := (35282499720324189037455055911656721727331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2499780377985479151714542946000000000000000)
      constant := (33483923480612191079096168862321477712819289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383466804277511977159/100000000000000000000)
  centralHi := (9586670106937799429/2500000000000000000)
  directionLo := (386702868436597653693/100000000000000000000)
  directionHi := (193351434218298826847/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree061.table
  base := (592702900144344723481759257330415887331/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-22412852586755574490732234805412200000000000000)
      constant := (304948726772356222670177276979165685613035366656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree061.table
  base := (37932677569152019952966982498953840886103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2544621355786686814903774258200000000000000)
      constant := (34729003586159643384900496910580122976835957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386702868436597653693/100000000000000000000)
  centralHi := (193351434218298826847/50000000000000000000)
  directionLo := (194956037949185758079/50000000000000000000)
  directionHi := (389912075898371516159/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree062.table
  base := (10161948768135247922800442286938205568597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-22807896618853347202577897195748400000000000000)
      constant := (316083027827196822241048485334711234814713354992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree062.table
  base := (40647526408283380828724641165386384998603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2589462333587894478093005570400000000000000)
      constant := (35996552903691855863565445542542341314973457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194956037949185758079/50000000000000000000)
  centralHi := (389912075898371516159/100000000000000000000)
  directionLo := (49136885554168708691/12500000000000000000)
  directionHi := (393095084433349669529/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree063.table
  base := (6948359437930540005409793340244231279/1600000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-23202940650951119914423559586084600000000000000)
      constant := (327414754378674504545946163367338040775272725000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree063.table
  base := (5428376528287159058706875384038913800109/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2634303311389102141282236882600000000000000)
      constant := (37286570786991829530384627210273914897616568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49136885554168708691/12500000000000000000)
  centralHi := (393095084433349669529/100000000000000000000)
  directionLo := (99063131348129203221/25000000000000000000)
  directionHi := (79250505078503362577/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree064.table
  base := (23135655027719815280759227958826870259489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-23597984683048892626269221976420800000000000000)
      constant := (338943901424287087125139599289784980573288102552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree064.table
  base := (23135552922060868817466530398117813685869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2679144289190309804471468194800000000000000)
      constant := (38599056681657197197782366772728476920063022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99063131348129203221/25000000000000000000)
  centralHi := (79250505078503362577/20000000000000000000)
  directionLo := (399385005169488126431/100000000000000000000)
  directionHi := (12480781411546503951/3125000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree065.table
  base := (6147495025163631262996446266773377262363/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-23993028715146665338114884366757000000000000000)
      constant := (350670464670174087978157427732274728346516399136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree065.table
  base := (12294945557087720221901092452841184704871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2723985266991517467660699507000000000000000)
      constant := (39934010112053246852456529783915930037570196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399385005169488126431/100000000000000000000)
  centralHi := (12480781411546503951/3125000000000000000)
  directionLo := (402493106560245244371/100000000000000000000)
  directionHi := (100623276640061311093/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree066.table
  base := (6519146871412912874347817162608552422227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-24388072747244438049960546757093200000000000000)
      constant := (362594440430715798569403763398556093718825261344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree066.table
  base := (10430603980428611543866779050401191011121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2768826244792725130849930819200000000000000)
      constant := (41291430670119987248748750581388113146056495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402493106560245244371/100000000000000000000)
  centralHi := (100623276640061311093/25000000000000000000)
  directionLo := (32446191202326531/8000000000000000)
  directionHi := (405577390029081637501/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree067.table
  base := (55190935521729423065367208343689991511133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-24783116779342210761806209147429400000000000000)
      constant := (374715825542357668966632025005488325534855052572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree067.table
  base := (55190800439833374411620570115182396715459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2813667222593932794039162131400000000000000)
      constant := (42671318005769785406007508892088465537593721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32446191202326531/8000000000000000)
  centralHi := (405577390029081637501/100000000000000000000)
  directionLo := (51079799361068162439/12500000000000000000)
  directionHi := (408638394888545299513/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree068.table
  base := (2914661283899765314170747988903844990951/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-25178160811439983473651871537765600000000000000)
      constant := (387034617289644478376481775839987062249216353680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree068.table
  base := (29146554016682101335803990076119982072121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2858508200395140457228393443600000000000000)
      constant := (44073671818649546386668532845292559318740598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51079799361068162439/12500000000000000000)
  centralHi := (408638394888545299513/100000000000000000000)
  directionLo := (82335328080082746717/20000000000000000000)
  directionHi := (205838320200206866793/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree069.table
  base := (61460031556455754027483749347857883167381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-25573204843537756185497533928101800000000000000)
      constant := (399550813341734336273590840079917247857672591804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree069.table
  base := (61459929120327947440955031511164631045013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2903349178196348120417624755800000000000000)
      constant := (45498491851073525884623341657812127989855247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82335328080082746717/20000000000000000000)
  centralHi := (205838320200206866793/50000000000000000000)
  directionLo := (82938525360813218877/20000000000000000000)
  directionHi := (207346313402033047193/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree070.table
  base := (16172835309959273942787792962813141296679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-25968248875635528897343196318438000000000000000)
      constant := (412264411697907669755301318650383185653806628944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree070.table
  base := (64691252064866605959185297102195603392499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2948190155997555783606856068000000000000000)
      constant := (46945777881960421847422883214941716464457481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82938525360813218877/20000000000000000000)
  centralHi := (207346313402033047193/50000000000000000000)
  directionLo := (52210854534752474337/12500000000000000000)
  directionHi := (417686836278019794697/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree071.table
  base := (16996786124662265632245263065961522709997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-26363292907733301609188858708774200000000000000)
      constant := (425175410640796734503262244743586012114580545392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree071.table
  base := (16996766720979214959727388707118462837803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-2993031133798763446796087380200000000000000)
      constant := (48415529721632031225706762296841003175673028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52210854534752474337/12500000000000000000)
  centralHi := (417686836278019794697/100000000000000000000)
  directionLo := (210329866919932574729/50000000000000000000)
  directionHi := (420659733839865149459/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree072.table
  base := (35673716276034084025403701332856564150599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-26758336939831074321034521099110400000000000000)
      constant := (438283808696241760351850751643576982831718325032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree072.table
  base := (3567368250617841848307032702192833438307/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3037872111599971109985318692400000000000000)
      constant := (49907747207351038449309223041233276706556660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210329866919932574729/50000000000000000000)
  centralHi := (420659733839865149459/100000000000000000000)
  directionLo := (423611768189354088743/100000000000000000000)
  directionHi := (52951471023669261093/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree073.table
  base := (18693049465675011251654832399934274609991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-27153380971928847032880183489446600000000000000)
      constant := (451589604598834831336235290513201538034494916176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree073.table
  base := (37386069550763195984715833405325666524067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3082713089401178773174550004600000000000000)
      constant := (51422430199492900756172773817302375327914546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423611768189354088743/100000000000000000000)
  centralHi := (52951471023669261093/12500000000000000000)
  directionLo := (85308674499794202477/20000000000000000000)
  directionHi := (213271686249485506193/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree074.table
  base := (39130716980210285264973307591958940352803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-27548425004026619744725845879782800000000000000)
      constant := (465092797262345629213101375293557969484379957704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree074.table
  base := (39130691423189168917639890901877493453997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3127554067202386436363781316800000000000000)
      constant := (52959578578261721593040861209871344751251886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85308674499794202477/20000000000000000000)
  centralHi := (213271686249485506193/50000000000000000000)
  directionLo := (429454965155929727613/100000000000000000000)
  directionHi := (214727482577964863807/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree075.table
  base := (3272605411647029296972315934806207642519/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-27943469036124392456571508270119000000000000000)
      constant := (478793385754337350198854929166447009096416494900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree075.table
  base := (20453772709298002231887725581315215020257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3172395045003594099553012629000000000000000)
      constant := (54519192240872808312826937381679956341539532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429454965155929727613/100000000000000000000)
  centralHi := (214727482577964863807/50000000000000000000)
  directionLo := (13510842201849846523/3125000000000000000)
  directionHi := (432346950459195088737/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree076.table
  base := (85433297087203941177486544498768957515829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-28338513068222165168417170660455200000000000000)
      constant := (492691369274379107599826974638662927663587435836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree076.table
  base := (42716629216179355666901256308382974079761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3217236022804801762742243941200000000000000)
      constant := (56101271099135595731194594533318553015030918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13510842201849846523/3125000000000000000)
  centralHi := (432346950459195088737/100000000000000000000)
  directionLo := (217609859637408529951/50000000000000000000)
  directionHi := (435219719274817059903/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree077.table
  base := (89115915255645536959782743375394243736291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-28733557100319937880262833050791400000000000000)
      constant := (506786747135345250285168188775534962215423478244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree077.table
  base := (89115881649244629868877573532841683431627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3262077000606009425931475253400000000000000)
      constant := (57705815077380041359625848921023991985200913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217609859637408529951/50000000000000000000)
  centralHi := (435219719274817059903/100000000000000000000)
  directionLo := (438073649652584609947/100000000000000000000)
  directionHi := (109518412413146152487/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree078.table
  base := (46431493141467146909304622408235142066623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-29128601132417710592108495441127600000000000000)
      constant := (521079518747364225977054413667246197181425871464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree078.table
  base := (92862957070562287952050502112202906093759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3306917978407217089120706565600000000000000)
      constant := (59332824110677683143086914468531855215781421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438073649652584609947/100000000000000000000)
  centralHi := (109518412413146152487/25000000000000000000)
  directionLo := (13778409606461054883/3125000000000000000)
  directionHi := (440909107406753756257/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree079.table
  base := (48337253576367421874507371029478034990313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-29523645164515483303954157831463800000000000000)
      constant := (535569683604041587753342404129190255852627415384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree079.table
  base := (24168620441011678371844105415764482000049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3351758956208424752309937877800000000000000)
      constant := (60982298143315486611754838518698100632003724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13778409606461054883/3125000000000000000)
  centralHi := (440909107406753756257/100000000000000000000)
  directionLo := (443726446663375244827/100000000000000000000)
  directionHi := (110931611665843811207/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree080.table
  base := (50275237637753382254576726586101325398181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-29918689196613256015799820221800000000000000000)
      constant := (550257241270634931366382122907722069826296438008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree080.table
  base := (20110090642709128791795515302890072834269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3396599934009632415499169190000000000000000)
      constant := (62654237127486558777827943713774556919255555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443726446663375244827/100000000000000000000)
  centralHi := (110931611665843811207/25000000000000000000)
  directionLo := (446526010376540183739/100000000000000000000)
  directionHi := (22326300518827009187/5000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree081.table
  base := (104490888428048007038450612367364427723583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-30313733228711028727645482612136200000000000000)
      constant := (565142191373904204011688036023147084583946008372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree081.table
  base := (104490869259901779211065269521813409205083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3441440911810840078688400502200000000000000)
      constant := (64348641022166910938346244808014454774896577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446526010376540183739/100000000000000000000)
  centralHi := (22326300518827009187/5000000000000000000)
  directionLo := (89861626163134828447/20000000000000000000)
  directionHi := (112327032703918535559/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree082.table
  base := (1695246010962558457793672045400859252841/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-30708777260808801439491145002472400000000000000)
      constant := (580224533593400009803141881307562882707453340416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree082.table
  base := (108495728050235585219504740505500401362127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3486281889612047741877631814400000000000000)
      constant := (66065509792151831946851181358004507625880413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89861626163134828447/20000000000000000000)
  centralHi := (112327032703918535559/25000000000000000000)
  directionLo := (220738833020429571/48828125000000000)
  directionHi := (452073130025839761409/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree083.table
  base := (22513008491465406464701419714644769134161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-31103821292906574151336807392808600000000000000)
      constant := (595504267653986169910797629152867387106597426620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree083.table
  base := (112565027994434892246591018269710979941443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3531122867413255405066863126600000000000000)
      constant := (67804843407229190578326358911024508618887417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220738833020429571/48828125000000000)
  centralHi := (452073130025839761409/100000000000000000000)
  directionLo := (227410660131426501437/50000000000000000000)
  directionHi := (3638570562102824023/800000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree084.table
  base := (116698780288049706785934707439465445375863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-31498865325004346863182469783144800000000000000)
      constant := (610981393319421662723883606998198816831481383892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree084.table
  base := (1166987677278271707532847319193780807777/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3575963845214463068256094438800000000000000)
      constant := (69566641841470208771530029420068183534776300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227410660131426501437/50000000000000000000)
  centralHi := (3638570562102824023/800000000000000000)
  directionLo := (57194125550609650143/12500000000000000000)
  directionHi := (91510600880975440229/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree085.table
  base := (4835878279418774246887060286587464168289/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-31893909357102119575028132173481000000000000000)
      constant := (626655910386851846691452003900808120860725761900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree085.table
  base := (120896946079155901520344685278575983362759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3620804823015670731445325751000000000000000)
      constant := (71350905072621012661296610157792943683892421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57194125550609650143/12500000000000000000)
  centralHi := (91510600880975440229/20000000000000000000)
  directionLo := (460268476342030675173/100000000000000000000)
  directionHi := (230134238171015337587/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree086.table
  base := (31289892877996274381868183423924315026079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-32288953389199892286873794563817200000000000000)
      constant := (642527818682080135179525931632389538815352987344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree086.table
  base := (31289890510776827085411834259068765217329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3665645800816878394634557063200000000000000)
      constant := (73157633081580640499709753839289226156517004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460268476342030675173/100000000000000000000)
  centralHi := (230134238171015337587/50000000000000000000)
  directionLo := (462968021345426543089/100000000000000000000)
  directionHi := (46296802134542654309/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree087.table
  base := (129486622976523439528836705896734375630591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-32683997421297664998719456954153400000000000000)
      constant := (658597118055509546170837094217146628918366139444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree087.table
  base := (25897322951348166264305939782601326195949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3710486778618086057823788375400000000000000)
      constant := (74986825851953221648751863687247125988615155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462968021345426543089/100000000000000000000)
  centralHi := (46296802134542654309/10000000000000000000)
  directionLo := (465651916416956457829/100000000000000000000)
  directionHi := (46565191641695645783/10000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree088.table
  base := (66939055306894461658866152148268549433327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-33079041453395437710565119344489600000000000000)
      constant := (674863808378659216850379013773766234306129340136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree088.table
  base := (133878103479268607516835999036933554351291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3755327756419293721013019687600000000000000)
      constant := (76838483369663786712502980036101737532674529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465651916416956457829/100000000000000000000)
  centralHi := (46565191641695645783/10000000000000000000)
  directionLo := (468320430621032247771/100000000000000000000)
  directionHi := (117080107655258061943/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree089.table
  base := (17291754220806788349806301379654501477891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-33474085485493210422410781734825800000000000000)
      constant := (691327889541174420506155660759797805608914021152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree089.table
  base := (17291753446838507050933667988281133813167/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3800168734220501384202250999800000000000000)
      constant := (78712605622628666661081261909318732339601384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468320430621032247771/100000000000000000000)
  centralHi := (117080107655258061943/25000000000000000000)
  directionLo := (470973825399410020041/100000000000000000000)
  directionHi := (235486912699705010021/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree090.table
  base := (17856798983734226425681806881832267260093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-33869129517590983134256444125162000000000000000)
      constant := (707989361448260165249470493478703726853547625696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree090.table
  base := (142854386496999296076033876155532429303909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3845009712021709047391482312000000000000000)
      constant := (80609192600472723738056188016955116156774271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470973825399410020041/100000000000000000000)
  centralHi := (235486912699705010021/50000000000000000000)
  directionLo := (236806177435069686793/50000000000000000000)
  directionHi := (473612354870139373587/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree091.table
  base := (29487836887792391932323695418825782772451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-34264173549688755846102106515498200000000000000)
      constant := (724848224018478360779553697386972213574850818420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree091.table
  base := (73719589888618566976050453375940553960521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3889850689822916710580713624200000000000000)
      constant := (82528244294286759284589613267385741050499798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236806177435069686793/50000000000000000000)
  centralHi := (473612354870139373587/100000000000000000000)
  directionLo := (119059066527901316609/25000000000000000000)
  directionHi := (476236266111605266437/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree092.table
  base := (30417682211386236070691285364206236996367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-34659217581786528557947768905834400000000000000)
      constant := (741904477181857042490800380410226399459490387140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree092.table
  base := (7604420350635857461597803810515632355503/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3934691667624124373769944936400000000000000)
      constant := (84469760696419389305410964830395940295091140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119059066527901316609/25000000000000000000)
  centralHi := (476236266111605266437/100000000000000000000)
  directionLo := (239422899716280576281/50000000000000000000)
  directionHi := (478845799432561152563/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree093.table
  base := (156802071365624830453266195862609209208389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-35054261613884301269793431296170600000000000000)
      constant := (759158120878267440525147801786414559478741178876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree093.table
  base := (156802067857538084247827155608197843904929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-3979532645425332036959176248600000000000000)
      constant := (86433741800298489904832570356455759034193651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239422899716280576281/50000000000000000000)
  centralHi := (478845799432561152563/100000000000000000000)
  directionLo := (481441188628988679423/100000000000000000000)
  directionHi := (1880629643081987029/390625000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree094.table
  base := (161580165057219595792109508650379000468613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35720000000000000000000000000000000000000000
      center := (213005)
      previous := (190631)
      next := (0)
      square := (8898442928106320717329680398800000000000000)
      linear := (-754240545659193063439129652904400000000000000)
      constant := (16523599043745339268226764426808453789673885636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree094.table
  base := (80790081007269697131705525788777483095951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-4024373623226539700148407560800000000000000)
      constant := (88420187600278010732864671071573544357646138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481441188628988679423/100000000000000000000)
  centralHi := (1880629643081987029/390625000000000000)
  directionLo := (96804532245712201347/20000000000000000000)
  directionHi := (30251416326785062921/6250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree095.table
  base := (33284538373420651727948037911760365475357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-35844349678079846693484756076843000000000000000)
      constant := (794257579670723400173906110282256760987324172940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree095.table
  base := (20802836153548028963913644518082906173007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-4069214601027747363337638873000000000000000)
      constant := (90429098091506551685726693424248601738297064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96804532245712201347/20000000000000000000)
  centralHi := (30251416326785062921/6250000000000000000)
  directionLo := (486590438723433210773/100000000000000000000)
  directionHi := (243295219361716605387/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree096.table
  base := (171329651567761308835153703023095842464533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-36239393710177619405330418467179200000000000000)
      constant := (812103394684148758203022263004435022416315658172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree096.table
  base := (10708103079976568845079597121457646859447/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-4114055578828955026526870185200000000000000)
      constant := (92460473269814610357083927022523124645271888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486590438723433210773/100000000000000000000)
  centralHi := (243295219361716605387/50000000000000000000)
  directionLo := (24457236839601693147/5000000000000000000)
  directionHi := (489144736792033862941/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree097.table
  base := (22037630495441183607537664802175820077859/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-36634437742275392117176080857515400000000000000)
      constant := (830146600063458118127166293134141158023610242848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree097.table
  base := (35260208395922510710018300492295943640119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-4158896556630162689716101497400000000000000)
      constant := (94514313131617847194215329758668114645811305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell035.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24457236839601693147/5000000000000000000)
  centralHi := (489144736792033862941/100000000000000000000)
  directionLo := (245842882755243171849/50000000000000000000)
  directionHi := (491685765510486343699/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree098.table
  base := (181336868886089454091736510703860641844453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10011235)
      previous := (8959657)
      next := (0)
      square := (418226817620997073714494978743600000000000000)
      linear := (-37029481774373164829021743247851600000000000000)
      constant := (848387195780393533050615504261916839995414147452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree098.table
  base := (90668433583063560331523383439143139493621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1130)
      previous := (1017)
      next := (0)
      square := (47332143234608088921966385100000000000000)
      linear := (-4203737534431370352905332809600000000000000)
      constant := (96590617673834092321561293171087439300757598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell035.Kernel098
