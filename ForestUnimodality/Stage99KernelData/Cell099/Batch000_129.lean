import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell099.Parameters
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch000_049
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch050_099
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch100_149
import ForestUnimodality.BinomialMassData.Q27_52.Batch000_049
import ForestUnimodality.BinomialMassData.Q27_52.Batch050_099
import ForestUnimodality.BinomialMassData.Q27_52.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree000.table
  base := (6092456547480203992272151903/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (782553719226750654769375610000000000000)
      linear := (-28108467247138680007723099000000000000)
      constant := (609245654748020399227215190300000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree000.table
  base := (6092456547480203992272151903/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (782553719226750654769375610000000000000)
      linear := (-28108467247138680007723099000000000000)
      constant := (609245654748020399227215190300000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree001.table
  base := (331579106552539696424758352344904944276883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-6081769721134959909843932659161470250000000000)
      constant := (2402753740246882795434597429822405871388669483723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree001.table
  base := (331269087937949792843875439253001376829837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-142088508689061176833330623286000000000000)
      constant := (56022597483346720236493556611925107684242453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9992600812897369001/20000000000000000000)
  directionHi := (24981502032243422503/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree002.table
  base := (95506195809787089092935909512585308726147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-11959992510760642764046858643653321500000000000)
      constant := (1389521225991467474696121265053913833070305407414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree002.table
  base := (190699450168595835869572578446768912788911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-279426686413355916745356042841000000000000)
      constant := (32375760529823644407130839866300946261325959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9992600812897369001/20000000000000000000)
  centralHi := (24981502032243422503/50000000000000000000)
  directionLo := (70658357964899368217/100000000000000000000)
  directionHi := (35329178982449684109/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree003.table
  base := (118043523114056151860459315915627701695639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-1982023922265147290916642736460574750000000000)
      constant := (96538441477301190706817018860300960910188900151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree003.table
  base := (29450266594885611646542796087218147519851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-416764864137650656657381462396000000000000)
      constant := (20236675706635902170946330346846842723419276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70658357964899368217/100000000000000000000)
  centralHi := (35329178982449684109/50000000000000000000)
  directionLo := (86538461538461538461/100000000000000000000)
  directionHi := (43269230769230769231/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree004.table
  base := (78666777928575872230423358681024032070539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-23716438090012008472452710612637024000000000000)
      constant := (594476184386043891218599354927264134157198828259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree004.table
  base := (3924687388415466205813784891836935235951/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-554103041861945396569406881951000000000000)
      constant := (13845791106164322679660178561847841097514380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86538461538461538461/100000000000000000000)
  centralHi := (43269230769230769231/50000000000000000000)
  directionLo := (99926008128973690011/100000000000000000000)
  directionHi := (24981502032243422503/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree005.table
  base := (56205321699430048503644500691395727042549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-29594660879637691326655636597128875250000000000)
      constant := (445646880077562529359251898106182812148867275069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree005.table
  base := (28041742333652393424729702917685978356317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-691441219586240136481432301506000000000000)
      constant := (10381819094585911741110270001629735684435146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/100000000000000000000)
  centralHi := (24981502032243422503/25000000000000000000)
  directionLo := (111720673448290871687/100000000000000000000)
  directionHi := (13965084181036358961/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree006.table
  base := (21221751777812404288826575608935243121169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-3941431518807041575650951397957858500000000000)
      constant := (40318286742814561648538578326506640846211335842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree006.table
  base := (1323609372629902675451576020608963953339/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-828779397310534876393457721061000000000000)
      constant := (8456462333149809945351657675379277059657312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111720673448290871687/100000000000000000000)
  centralHi := (13965084181036358961/12500000000000000000)
  directionLo := (61191932987297381919/50000000000000000000)
  directionHi := (122383865974594763839/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree007.table
  base := (33308174381886550435467473698836488162491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-41351106458889057035061488566112577750000000000)
      constant := (316633654280928868843849628618377665736965989171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree007.table
  base := (33241520952585341514205410122278615201709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-966117575034829616305483140616000000000000)
      constant := (7382182754774650158784012359526460969088821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61191932987297381919/50000000000000000000)
  centralHi := (122383865974594763839/100000000000000000000)
  directionLo := (132189683508341538651/100000000000000000000)
  directionHi := (33047420877085384663/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree008.table
  base := (6689033355953408391613730791198574525387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-47229329248514739889264414550604429000000000000)
      constant := (292158301422170825253683296767360770610695912588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree008.table
  base := (13351425636316648683759123946382846128841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-1103455752759124356217508560171000000000000)
      constant := (6814440654347723517783504788135401991548258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132189683508341538651/100000000000000000000)
  centralHi := (33047420877085384663/25000000000000000000)
  directionLo := (70658357964899368217/50000000000000000000)
  directionHi := (28263343185959747287/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree009.table
  base := (2174297661681946837338619286869699629657/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-655648790594326206709473339939460250000000000)
      constant := (3479944319988029168434747307822185267472154570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree009.table
  base := (2712285953530405532309726530700202944289/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-1240793930483419096129533979726000000000000)
      constant := (6577272681595311015561153361622549380678728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70658357964899368217/50000000000000000000)
  centralHi := (28263343185959747287/20000000000000000000)
  directionLo := (18736126524182566877/12500000000000000000)
  directionHi := (149889012193460535017/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree010.table
  base := (708753999758479924607456452708744336469/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-58985774827766105597670266519588131500000000000)
      constant := (281803462717121949021027732624345444441196764725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree010.table
  base := (17680002704056994010435868254862589550773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-1378132108207713836041559399281000000000000)
      constant := (6578096020221878850263406377506777634080637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18736126524182566877/12500000000000000000)
  centralHi := (149889012193460535017/100000000000000000000)
  directionLo := (78998445794014343287/50000000000000000000)
  directionHi := (6319875663521147463/4000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree011.table
  base := (14381333160964432974760226271833753950871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-64863997617391788451873192504079982750000000000)
      constant := (289752248277277702185633430405154851557969779951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree011.table
  base := (7173387066257351433592440706794120230953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-1515470285932008575953584818836000000000000)
      constant := (6766004090109813427091190504111787638062114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78998445794014343287/50000000000000000000)
  centralHi := (6319875663521147463/4000000000000000000)
  directionLo := (2071356723511308411/1250000000000000000)
  directionHi := (165708537880904672881/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree012.table
  base := (2888482618808566649206755845187223100663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-7860246711890830145119568720952426000000000000)
      constant := (33827084084120132958098645198894134442205423068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree012.table
  base := (11522780411937749264657352462112762660879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-1652808463656303315865610238391000000000000)
      constant := (7111283057475427701717098366554056889688551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2071356723511308411/1250000000000000000)
  centralHi := (165708537880904672881/100000000000000000000)
  directionLo := (173076923076923076923/100000000000000000000)
  directionHi := (43269230769230769231/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree013.table
  base := (9125986751470855365941182280842518343187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (33531644315147038806212975512890000000000000)
      linear := (-453375403530432864853722156645347250000000000)
      constant := (1923530655234475398247160327707954420049719763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree013.table
  base := (1819546099004095625659942770954124322551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (782553719226750654769375610000000000000)
      linear := (-10592583676808272519394293834000000000000)
      constant := (44942566481207490926281521003645621612755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173076923076923076923/100000000000000000000)
  centralHi := (43269230769230769231/25000000000000000000)
  directionLo := (11259010814420189073/6250000000000000000)
  directionHi := (180144173030723025169/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree014.table
  base := (7022694976877847821410506643662771109263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-82498665986268837014481970457555536500000000000)
      constant := (351109306648081603256355509622192204176326938503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree014.table
  base := (3498503363735911036439210541825787132937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-1927484819104892795689661077501000000000000)
      constant := (8205425740080537833460157531461116050932706) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11259010814420189073/6250000000000000000)
  centralHi := (180144173030723025169/100000000000000000000)
  directionLo := (46736110805825915127/25000000000000000000)
  directionHi := (186944443223303660509/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree015.table
  base := (5189891043629873439354409952631746402827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-9819654308432724429853877382449709750000000000)
      constant := (42461045126638623057111415108892872505494729643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree015.table
  base := (206661595416667338471543261798670575113/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-2064822996829187535601686497056000000000000)
      constant := (8932541372909951801886612962048758179852425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46736110805825915127/25000000000000000000)
  centralHi := (186944443223303660509/100000000000000000000)
  directionLo := (9675294133412551571/5000000000000000000)
  directionHi := (193505882668251031421/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree016.table
  base := (3586152004987623329308805256057431595793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-94255111565520202722887822426539239000000000000)
      constant := (417897015727847637793285007613149614809734689433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree016.table
  base := (3564953030928419589930395402717608024573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-2202161174553482275513711916611000000000000)
      constant := (9769647931302705254659077169095275756152837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9675294133412551571/5000000000000000000)
  centralHi := (193505882668251031421/100000000000000000000)
  directionLo := (99926008128973690011/50000000000000000000)
  directionHi := (199852016257947380023/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree017.table
  base := (217853268536402428875470782839186585057/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-100133334355145885577090748411031090250000000000)
      constant := (458113563549326239652551944492187717963013994170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree017.table
  base := (269915381672635083223737718222791906393/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-2339499352277777015425737336166000000000000)
      constant := (10711181409563012677011690758621089657443336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/50000000000000000000)
  centralHi := (199852016257947380023/100000000000000000000)
  directionLo := (103001371565521874971/50000000000000000000)
  directionHi := (206002743131043749943/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree018.table
  base := (940140586429073955062020390871386436267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-1308784656108290968287576227105221500000000000)
      constant := (6204991457882520608060031940059646850038706067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree018.table
  base := (922768698730202607959360812832213659041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-2476837530002071755337762755721000000000000)
      constant := (11752598875757359639186545710961644108377929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103001371565521874971/50000000000000000000)
  centralHi := (206002743131043749943/100000000000000000000)
  directionLo := (211975073894698104651/100000000000000000000)
  directionHi := (52993768473674526163/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree019.table
  base := (-37834772291060197834740657745097413589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-111889779934397251285496600380014792750000000000)
      constant := (551207657164314180682102184477915832984446958764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree019.table
  base := (-83508903897908917850027627077694888601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-2614175707726366495249788175276000000000000)
      constant := (12890130315949345191572180118111114127652862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211975073894698104651/100000000000000000000)
  centralHi := (52993768473674526163/25000000000000000000)
  directionLo := (10889184281640504371/5000000000000000000)
  directionHi := (217783685632810087421/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree020.table
  base := (-557304983990428561380504333543346949327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-117768002724022934139699526364506644000000000000)
      constant := (603788168820415186140774105090233120155081133426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree020.table
  base := (-1128734186172725091562820868124402025833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-2751513885450661235161813594831000000000000)
      constant := (14120615815463068526111307804281976057634223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10889184281640504371/5000000000000000000)
  centralHi := (217783685632810087421/100000000000000000000)
  directionLo := (1787530775172653947/800000000000000000)
  directionHi := (13965084181036358961/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree021.table
  base := (-1965445073814724194019422531187324911929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-13738469501516512999322494705444277250000000000)
      constant := (73359069222741194989924140073764218416500219239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree021.table
  base := (-494536842521070145266767979504704769883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-2888852063174955975073839014386000000000000)
      constant := (15441390762505973962580883804242694575559092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1787530775172653947/800000000000000000)
  centralHi := (13965084181036358961/6250000000000000000)
  directionLo := (228959248072897262639/100000000000000000000)
  directionHi := (2861990600911215783/1250000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree022.table
  base := (-1358597931159214393241008414632835351347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-129524448303274299848105378333490346500000000000)
      constant := (720441335404650337209605482201061179185434750186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree022.table
  base := (-341075266731492330625759531544044265907/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-3026190240899250714985864433941000000000000)
      constant := (16850199890217735717386845851594452152493736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228959248072897262639/100000000000000000000)
  centralHi := (2861990600911215783/1250000000000000000)
  directionLo := (58586815418047791061/25000000000000000000)
  directionHi := (46869452334438232849/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree023.table
  base := (-1690595251222923446927918370128737804173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1670058)
      previous := (835029)
      next := (835029)
      square := (10712377862494989713137982725290000000000000)
      linear := (-255959680704914901138579025175769750000000000)
      constant := (1482675374858430340561158946072548142959851606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree023.table
  base := (-3391419375565569204479227517979892713329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-3163528418623545454897889853496000000000000)
      constant := (18345129966821165773863396420018773131447399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58586815418047791061/25000000000000000000)
  centralHi := (46869452334438232849/20000000000000000000)
  directionLo := (14975884368241721489/6250000000000000000)
  directionHi := (9584565995674701753/4000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree024.table
  base := (-1983527616632319276660209135676946913591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-15697877098058407284056803366941561000000000000)
      constant := (94649303162637641764151684210326413841604918162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree024.table
  base := (-3976217638547323037493790975150780115673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-3300866596347840194809915273051000000000000)
      constant := (19924555458494820650527307680533518160451263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14975884368241721489/6250000000000000000)
  centralHi := (9584565995674701753/4000000000000000000)
  directionLo := (244767731949189527677/100000000000000000000)
  directionHi := (122383865974594763839/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree025.table
  base := (-448297882387234615302996551508137128119/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-147159116672151348410714156286965900250000000000)
      constant := (922907402079704474020628414456587949889879457610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree025.table
  base := (-1122794444647605428017219707648754858719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-3438204774072134934721940692606000000000000)
      constant := (21587093800609645902383349670201316715505956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244767731949189527677/100000000000000000000)
  centralHi := (122383865974594763839/50000000000000000000)
  directionLo := (249815020322434225027/100000000000000000000)
  directionHi := (62453755080608556257/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree026.table
  base := (-1233983220862300030853272807738163346969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (33531644315147038806212975512890000000000000)
      linear := (-905546387347793084407793386221643500000000000)
      constant := (5902223724098157871888001366916920286232901276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree026.table
  base := (-4943263469547922838141351624328777315763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (782553719226750654769375610000000000000)
      linear := (-21157058886369406358780864569000000000000)
      constant := (138056616167363756173681615134671222684237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249815020322434225027/100000000000000000000)
  centralHi := (62453755080608556257/25000000000000000000)
  directionLo := (254762332682534043887/100000000000000000000)
  directionHi := (15922645792658377743/6250000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree027.table
  base := (-2665928377695773494152528933424712098827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-1961920521622255729865679114270982750000000000)
      constant := (13277851119753509580752191449428441416368034746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree027.table
  base := (-667300782513302780124616049605552336597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-3712881129520724414545991531716000000000000)
      constant := (25156976021791272628960551025364668240920856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254762332682534043887/100000000000000000000)
  centralHi := (15922645792658377743/6250000000000000000)
  directionLo := (32451923076923076923/12500000000000000000)
  directionHi := (51923076923076923077/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree028.table
  base := (-709476672864761211531248842124919343287/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-164793785041028396973322934240441454000000000000)
      constant := (1156961132854918944878633906516221919467437695624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree028.table
  base := (-1136332312839565754751362836501089996303/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-3850219307245019154458016951271000000000000)
      constant := (27062463104175546813030940222209578953123965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32451923076923076923/12500000000000000000)
  centralHi := (51923076923076923077/20000000000000000000)
  directionLo := (264379367016683077303/100000000000000000000)
  directionHi := (33047420877085384663/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree029.table
  base := (-93314391573659549126047875107566662811/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-170672007830654079827525860224933305250000000000)
      constant := (1241810114988326085550252646191486557185389662176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree029.table
  base := (-5977340501950027505525305513876815835983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-3987557484969313894370042370826000000000000)
      constant := (29047300800135684768884734434290693123718873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264379367016683077303/100000000000000000000)
  centralHi := (33047420877085384663/12500000000000000000)
  directionLo := (134529505573396370849/50000000000000000000)
  directionHi := (269059011146792741699/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree030.table
  base := (-622446499161772799468634283738684850237/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-19616692291142195853525420689936128500000000000)
      constant := (147780688974880500299621114137578192244606576670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree030.table
  base := (-1245824303061934434747532866942188215137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-4124895662693608634282067790381000000000000)
      constant := (31110867452982702014895374393113850958209235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134529505573396370849/50000000000000000000)
  centralHi := (269059011146792741699/100000000000000000000)
  directionLo := (17103665229276090137/6250000000000000000)
  directionHi := (273658643668417442193/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree031.table
  base := (-3217995923791414789524885021097506965357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-182428453409905445535931712193917007750000000000)
      constant := (1421586603646544701378261334667965877052561752566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree031.table
  base := (-1610036240833398989499586569081064573169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-4262233840417903374194093209936000000000000)
      constant := (33252632342035993743709707096986575348537756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17103665229276090137/6250000000000000000)
  centralHi := (273658643668417442193/100000000000000000000)
  directionLo := (69545558372545348527/25000000000000000000)
  directionHi := (278182233490181394109/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree032.table
  base := (-6609389985164589445597089858467837803673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-188306676199531128390134638178408859000000000000)
      constant := (1516471855923271891040637580942526061433620240287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree032.table
  base := (-6613093352808154275358290079962966248327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-4399572018142198114106118629491000000000000)
      constant := (35472142123648665889846123898638258704032737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69545558372545348527/25000000000000000000)
  centralHi := (278182233490181394109/100000000000000000000)
  directionLo := (70658357964899368217/25000000000000000000)
  directionHi := (282633431859597472869/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree033.table
  base := (-6746957530656455146863140672814566375801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-21576099887684090138259729351433412250000000000)
      constant := (179407257307357385645282359116353641351995633191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree033.table
  base := (-1687564856007080190374875973696432296539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-4536910195866492854018144049046000000000000)
      constant := (37769009324710867908874365420861086767539636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70658357964899368217/25000000000000000000)
  centralHi := (282633431859597472869/100000000000000000000)
  directionLo := (35876950857209854137/12500000000000000000)
  directionHi := (287015606857678833097/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree034.table
  base := (-6850660196280253564747824881165209088397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-200063121778782494098540490147392561500000000000)
      constant := (1716152748507672613528404900879954368556595804043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree034.table
  base := (-1370720791406344967492158830070340855339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-4674248373590787593930169468601000000000000)
      constant := (40142902573396240428638873377059561977238545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35876950857209854137/12500000000000000000)
  centralHi := (287015606857678833097/100000000000000000000)
  directionLo := (58266374644396603577/20000000000000000000)
  directionHi := (145665936610991508943/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree035.table
  base := (-3461090198303933943043246681628888012343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-205941344568408176952743416131884412750000000000)
      constant := (1820921970974483903971540943916884765604043300034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree035.table
  base := (-69248048706023165315387434728546339903/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-4811586551315082333842194888156000000000000)
      constant := (42593538301430295894357525303406941855639300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58266374644396603577/20000000000000000000)
  centralHi := (145665936610991508943/50000000000000000000)
  directionLo := (147792559124417284373/50000000000000000000)
  directionHi := (295585118248834568747/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree036.table
  base := (-6962958990615963345874989539538133698451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-2615056387136220491443782001436744000000000000)
      constant := (23814352459428977054251437357405434684224782149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree036.table
  base := (-3482649470957324533009511145863116363443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-4948924729039377073754220307711000000000000)
      constant := (45120673693470534811464042897329266669156266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147792559124417284373/50000000000000000000)
  centralHi := (295585118248834568747/100000000000000000000)
  directionLo := (299778024386921070033/100000000000000000000)
  directionHi := (149889012193460535017/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree037.table
  base := (-3487115385105850311317180551102531923941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-217697790147659542661149268100868115250000000000)
      constant := (2040265541503327667979424072015669373830838106758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree037.table
  base := (-3488158634783457934691922311779168704859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-5086262906763671813666245727266000000000000)
      constant := (47724100693853862490544931990022515977757658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299778024386921070033/100000000000000000000)
  centralHi := (149889012193460535017/50000000000000000000)
  directionLo := (303913089024598236011/100000000000000000000)
  directionHi := (75978272256149559003/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree038.table
  base := (-6957054643807658226152263071540055463249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-223576012937285225515352194085359966500000000000)
      constant := (2154823279778075056287078264250449241655186168231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree038.table
  base := (-1391783086006647155914414484262434445951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-5223601084487966553578271146821000000000000)
      constant := (50403640910156152847988524911436242893171405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303913089024598236011/100000000000000000000)
  centralHi := (75978272256149559003/25000000000000000000)
  directionLo := (307992641885518592619/100000000000000000000)
  directionHi := (15399632094275929631/5000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree039.table
  base := (-6912339318162098829766703566809813460333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3725738257238559867356997279210000000000000)
      linear := (-150857485685017033773540512866437750000000000)
      constant := (1494167773606354224572874825957044204677854587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree039.table
  base := (-6913999131835313306849278389011564351803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (782553719226750654769375610000000000000)
      linear := (-31721534095930540198167435304000000000000)
      constant := (314551131820338685334674200441363435648197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307992641885518592619/100000000000000000000)
  centralHi := (15399632094275929631/5000000000000000000)
  directionLo := (62403772075338276227/20000000000000000000)
  directionHi := (19501178773543211321/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree040.table
  base := (-6840865158879595039828623396032632051237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-235332458516536591223758046054343669000000000000)
      constant := (2393677602132198259802206292912925229620976238003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree040.table
  base := (-6842346048620219847630005646435758927031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-5498277439936556033402321985931000000000000)
      constant := (55990470369450762345265119092242356741331761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62403772075338276227/20000000000000000000)
  centralHi := (19501178773543211321/6250000000000000000)
  directionLo := (78998445794014343287/25000000000000000000)
  directionHi := (315993783176057373149/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree041.table
  base := (-8429128507635585990452577184168207263/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-241210681306162274077960972038835520250000000000)
      constant := (2517963678780983598486068016823161974767301297600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree041.table
  base := (-1686156102060782470299331206910640162101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-5635615617660850773314347405486000000000000)
      constant := (58897515255089201932105223627236282250419724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78998445794014343287/25000000000000000000)
  centralHi := (315993783176057373149/100000000000000000000)
  directionLo := (63983864460054329781/20000000000000000000)
  directionHi := (159959661150135824453/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree042.table
  base := (-662022903410164666998911565281614921313/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-27454322677309772992462655335925263500000000000)
      constant := (293942581877980770509386104019251340029022683830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree042.table
  base := (-1655352206726471856877289380273384872403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-5772953795385145513226372825041000000000000)
      constant := (61880178824414444942707364731122191826255572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63983864460054329781/20000000000000000000)
  centralHi := (159959661150135824453/50000000000000000000)
  directionLo := (32379727385543723529/10000000000000000000)
  directionHi := (323797273855437235291/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree043.table
  base := (-3236070134468722840199680516202274528867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-252967126885413639786366824007819222750000000000)
      constant := (2776232681634714230974266133041015386348913835946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree043.table
  base := (-3236596901447679343004644146441276508067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-5910291973109440253138398244596000000000000)
      constant := (64938377507216010989365542812230223540273354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32379727385543723529/10000000000000000000)
  centralHi := (323797273855437235291/100000000000000000000)
  directionLo := (327629327642323477551/100000000000000000000)
  directionHi := (20476832977645217347/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree044.table
  base := (-1574866028933648838178676575837164790897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-258845349675039322640569749992311074000000000000)
      constant := (2910208916485302705026166360939174016166401606172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree044.table
  base := (-1575101305349861497843243909907893445957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-6047630150833734993050423664151000000000000)
      constant := (68072039328897144577519639184631264030533068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327629327642323477551/100000000000000000000)
  centralHi := (20476832977645217347/6250000000000000000)
  directionLo := (2071356723511308411/625000000000000000)
  directionHi := (331417075761809345761/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree045.table
  base := (-1525642298344728282574757511453806370663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-3268192252650185253021884888602505250000000000)
      constant := (37622336692678203315488734778310536815687928548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree045.table
  base := (-6103410168484003345618307544774248130533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-6184968328558029732962449083706000000000000)
      constant := (71281102251912716380828596979125027065939923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2071356723511308411/625000000000000000)
  centralHi := (331417075761809345761/100000000000000000000)
  directionLo := (335162020344872615063/100000000000000000000)
  directionHi := (41895252543109076883/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree046.table
  base := (-5881773529620191633515589133136047531319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1670058)
      previous := (835029)
      next := (835029)
      square := (10712377862494989713137982725290000000000000)
      linear := (-511534584601683720886532328849328500000000000)
      constant := (6026146399825523488743343787536109926593774209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree046.table
  base := (-5882525307097856896613209790385808865003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-6322306506282324472874474503261000000000000)
      constant := (74565512760224374780302736738540798301814493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335162020344872615063/100000000000000000000)
  centralHi := (41895252543109076883/12500000000000000000)
  directionLo := (338865580513578766931/100000000000000000000)
  directionHi := (84716395128394691733/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree047.table
  base := (-5637351731140889661791324093705590885519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-276480018043916371203178527945786627750000000000)
      constant := (3331473448128531577568757399905021540485303486361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree047.table
  base := (-112760480593501354772431539295438040829/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-6459644684006619212786499922816000000000000)
      constant := (77925224650510763451011460277454923554994950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338865580513578766931/100000000000000000000)
  centralHi := (84716395128394691733/25000000000000000000)
  directionLo := (171264549332277652423/50000000000000000000)
  directionHi := (342529098664555304847/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree048.table
  base := (-2684770555390819188944201485849952675381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-31373137870393561561931272658919831000000000000)
      constant := (386481506830332993114669219836411513855628737942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree048.table
  base := (-2685071284729185452170796657606537405487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-6596982861730913952698525342371000000000000)
      constant := (81360197999353860172428774458076990356945394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171264549332277652423/50000000000000000000)
  centralHi := (342529098664555304847/100000000000000000000)
  directionLo := (173076923076923076923/50000000000000000000)
  directionHi := (346153846153846153847/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree049.table
  base := (-1015709385327005045840592284886372336633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-288236463623167736911584379914770330250000000000)
      constant := (3628410299168520438693867983638794739178295132635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree049.table
  base := (-634885653146893875368603272323327224551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-6734321039455208692610550761926000000000000)
      constant := (84870398280268736945604008400474736592407048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173076923076923076923/50000000000000000000)
  centralHi := (346153846153846153847/100000000000000000000)
  directionLo := (349741028451407915039/100000000000000000000)
  directionHi := (2185881427821299469/625000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree050.table
  base := (-1191136716107455568202305948300598418417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-294114686412793419765787305899262181500000000000)
      constant := (3781702374507273205549658504081026656588862977692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree050.table
  base := (-1191257207599076424122524359736289845491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-6871659217179503432522576181481000000000000)
      constant := (88455795608381912065651249206243268064448084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349741028451407915039/100000000000000000000)
  centralHi := (2185881427821299469/625000000000000000)
  directionLo := (176645894912248420543/50000000000000000000)
  directionHi := (353291789824496841087/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree051.table
  base := (-4427694874881059390902699148699050971367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-33332545466935455846665581320417114750000000000)
      constant := (437578741406453045921449280292631981023541869497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree051.table
  base := (-4428126579155370335185487483615713425187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-7008997394903798172434601601036000000000000)
      constant := (92116364093901718058383303289924319431143397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176645894912248420543/50000000000000000000)
  centralHi := (353291789824496841087/100000000000000000000)
  directionLo := (356807217601528316811/100000000000000000000)
  directionHi := (89201804400382079203/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree052.table
  base := (-203406223046714819501625289841942944327/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (33531644315147038806212975512890000000000000)
      linear := (-1809888354982513523515935845374236000000000000)
      constant := (24248096016934256488464697772294248110570647540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree052.table
  base := (-4068511302656096493762300894012973152971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (782553719226750654769375610000000000000)
      linear := (-42286009305491674037554006039000000000000)
      constant := (567172078629317875193321042468987026847029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356807217601528316811/100000000000000000000)
  centralHi := (89201804400382079203/25000000000000000000)
  directionLo := (360288346061446050337/100000000000000000000)
  directionHi := (180144173030723025169/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree053.table
  base := (-3685951495625914823619526053015965575111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-311749354781670468328396083852737735250000000000)
      constant := (4260860198026317635994281902442984229630242120609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree053.table
  base := (-737259655538194618390498754467263661661/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-7283673750352387652258652440146000000000000)
      constant := (99662927709962989986080407286975037205896455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360288346061446050337/100000000000000000000)
  centralHi := (180144173030723025169/50000000000000000000)
  directionLo := (181868079994016704777/50000000000000000000)
  directionHi := (72747231997606681911/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree054.table
  base := (-3281276639226700311522817373485107645301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-3921328118164150014599987775768266500000000000)
      constant := (54654368607678073243246973730396045922652445299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree054.table
  base := (-656317527068310899017541069414648701747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-7421011928076682392170677859701000000000000)
      constant := (103548886436573742605869709589458621847023785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181868079994016704777/50000000000000000000)
  centralHi := (72747231997606681911/20000000000000000000)
  directionLo := (73430319584756858303/20000000000000000000)
  directionHi := (91787899480946072879/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree055.table
  base := (-1427093707052322288053383849486058694209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-323505800360921834036801935821721437750000000000)
      constant := (4596358570657143349611043842325619160253563932942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree055.table
  base := (-356808303538059027425140156231863980253/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-7558350105800977132082703279256000000000000)
      constant := (107509942756281248040795754712963894898697944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73430319584756858303/20000000000000000000)
  centralHi := (91787899480946072879/25000000000000000000)
  directionLo := (370535555153801798657/100000000000000000000)
  directionHi := (185267777576900899329/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree056.table
  base := (-150297499191032329400248853768830612159/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-329384023150547516891004861806213289000000000000)
      constant := (4768923786771564248414586614118976404677315720336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree056.table
  base := (-1202505203252949040002467093454521954401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-7695688283525271871994728698811000000000000)
      constant := (111546083867347983254104582090138371579412462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370535555153801798657/100000000000000000000)
  centralHi := (185267777576900899329/50000000000000000000)
  directionLo := (373888886446607321017/100000000000000000000)
  directionHi := (186944443223303660509/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree057.table
  base := (-966530350740412741136199635837111342407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-37251360660019244416134198643411682250000000000)
      constant := (549411002793414096067616064914463428023856992274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree057.table
  base := (-193328554329609442482784363330265374229/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-7833026461249566611906754118366000000000000)
      constant := (115657298620277753908996241509695726517552990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373888886446607321017/100000000000000000000)
  centralHi := (186944443223303660509/50000000000000000000)
  directionLo := (377212408575635211251/100000000000000000000)
  directionHi := (94303102143908802813/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree058.table
  base := (-143914739549791803396575524634106242679/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-341140468729798882599410713775196991500000000000)
      constant := (5123683866930981616483194955554161119697836324010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree058.table
  base := (-1439349348254867156830047108332816068683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-7970364638973861351818779537921000000000000)
      constant := (119843577295951572807870459590874754084392573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377212408575635211251/100000000000000000000)
  centralHi := (94303102143908802813/25000000000000000000)
  directionLo := (380506902642488053007/100000000000000000000)
  directionHi := (23781681415155503313/6250000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree059.table
  base := (-923070536797395757495008321602841972611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-347018691519424565453613639759688842750000000000)
      constant := (5305877946681513145715946178602997785723397423109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree059.table
  base := (-461625998659605541871746733107993085107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-8107702816698156091730804957476000000000000)
      constant := (124104911414636087828220536977312873337233834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380506902642488053007/100000000000000000000)
  centralHi := (23781681415155503313/6250000000000000000)
  directionLo := (95943279055168779267/25000000000000000000)
  directionHi := (383773116220675117069/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree060.table
  base := (-76974840093142128761136125467493260119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-39210768256561138700868507304908966000000000000)
      constant := (610142327247046704095217120315343385452344557645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree060.table
  base := (-192518653211552840997971298298451020111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-8245040994422450831642830377031000000000000)
      constant := (128441293571438456438530182247660123555202482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95943279055168779267/25000000000000000000)
  centralHi := (383773116220675117069/100000000000000000000)
  directionLo := (9675294133412551571/2500000000000000000)
  directionHi := (387011765336502062841/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree061.table
  base := (21925385975399140487895116736363999821/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-358775137098675931162019491728672545250000000000)
      constant := (5679892583573622481288522106066792007474364699208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree061.table
  base := (43814107251223027669503423119274578917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-8382379172146745571554855796586000000000000)
      constant := (132852717294431252516322249386356504615347892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9675294133412551571/2500000000000000000)
  centralHi := (387011765336502062841/100000000000000000000)
  directionLo := (15608941452079249497/4000000000000000000)
  directionHi := (195111768150990618713/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree062.table
  base := (757727623986682450070259433405253297001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-364653359888301614016222417713164396500000000000)
      constant := (5871712617665080057879172221903969263331670098481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree062.table
  base := (757595709610530481873575443569174411213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-8519717349871040311466881216141000000000000)
      constant := (137339176922223607505300327200595190475494997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15608941452079249497/4000000000000000000)
  centralHi := (195111768150990618713/50000000000000000000)
  directionLo := (49176135926631691921/12500000000000000000)
  directionHi := (393409087413053535369/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree063.table
  base := (681034948580855142450613107468419769711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-4574463983678114776178090662934027750000000000)
      constant := (74898034985123512703156942110970824493226366222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree063.table
  base := (340487801613988760255721078121082296833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-8657055527595335051378906635696000000000000)
      constant := (141900667498225024013458447630207226632659108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49176135926631691921/12500000000000000000)
  centralHi := (393409087413053535369/100000000000000000000)
  directionLo := (198284525262512307977/50000000000000000000)
  directionHi := (79313810105004923191/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree064.table
  base := (397680809223193479723948513305860540587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-376409805467552979724628269682148099000000000000)
      constant := (6264977044689918320264592527118218057466552446735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree064.table
  base := (1988297220210406975457438284188894390173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-8794393705319629791290932055251000000000000)
      constant := (146537184679248603801455633834651923151939237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198284525262512307977/50000000000000000000)
  centralHi := (79313810105004923191/20000000000000000000)
  directionLo := (99926008128973690011/25000000000000000000)
  directionHi := (79940806503178952009/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree065.table
  base := (527341477839388566373938884641047164323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (33531644315147038806212975512890000000000000)
      linear := (-2262059338799873743070007074950532250000000000)
      constant := (38262846663319915533084874544718026188782881135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree065.table
  base := (527322242656440913772026981929757410771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (782553719226750654769375610000000000000)
      linear := (-52850484515052807876940576774000000000000)
      constant := (894962867789593802717362695266523787053855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/25000000000000000000)
  centralHi := (79940806503178952009/20000000000000000000)
  directionLo := (80562923329436199057/20000000000000000000)
  directionHi := (201407308323590497643/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree066.table
  base := (3306960017176712365655890369193493463617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-43129583449644927270337124627903533500000000000)
      constant := (741230312650683445059408067341928004363517410753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree066.table
  base := (3306873404703494663448113591332676409061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-9069070060768219271114982894361000000000000)
      constant := (156035284086819703403129129185396222313131309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80562923329436199057/20000000000000000000)
  centralHi := (201407308323590497643/50000000000000000000)
  directionLo := (101475340957718427863/25000000000000000000)
  directionHi := (405901363830873711453/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree067.table
  base := (3999144440379090275952196853102306682971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-394044473836430028287237047635623652750000000000)
      constant := (6878932101304016366521572461562368879189970020051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree067.table
  base := (1999533209522226905156634799923370448921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-9206408238492514011027008313916000000000000)
      constant := (160896860033936015870274665191445474211735298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101475340957718427863/25000000000000000000)
  centralHi := (405901363830873711453/100000000000000000000)
  directionLo := (204482406905160940427/50000000000000000000)
  directionHi := (81792962762064376171/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree068.table
  base := (2356622641284339797589613172613819856043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-399922696626055711141439973620115504000000000000)
      constant := (7089998837097945329383859613724408235024916239366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree068.table
  base := (4713174981883235160795752358393978314179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-9343746416216808750939033733471000000000000)
      constant := (165833449916412997943247388770711582335096251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204482406905160940427/50000000000000000000)
  centralHi := (81792962762064376171/20000000000000000000)
  directionLo := (103001371565521874971/25000000000000000000)
  directionHi := (82401097252417499977/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree069.table
  base := (5449249015170625995302883458874393836877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (185562)
      previous := (92781)
      next := (92781)
      square := (1190264206943887745904220302810000000000000)
      linear := (-85234387610939171181609514724765250000000000)
      constant := (1534188809760768773246651416397506804588389917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree069.table
  base := (1362296413856065661122474719170029291821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-9481084593941103490851059153026000000000000)
      constant := (170845051463263197266148742877834814801270996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103001371565521874971/25000000000000000000)
  centralHi := (82401097252417499977/20000000000000000000)
  directionLo := (415023881825139191099/100000000000000000000)
  directionHi := (4150238818251391911/1000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree070.table
  base := (6207143726302918452237973089736519317389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-411679142205307076849845825589099206500000000000)
      constant := (7521754273563573509579212318065608586674255413109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree070.table
  base := (96985728261997579950912756635085547829/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-9618422771665398230763084572581000000000000)
      constant := (175931662675064566035551925041435085285318464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415023881825139191099/100000000000000000000)
  centralHi := (4150238818251391911/1000000000000000000)
  directionLo := (209010241531578440967/50000000000000000000)
  directionHi := (83604096612631376387/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree071.table
  base := (6986918919883142989923720137989550516581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-417557364994932759704048751573591057750000000000)
      constant := (7742442811968424094597795829784992333865923996461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree071.table
  base := (1746716854527938573978068380952697705141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-9755760949389692970675109992136000000000000)
      constant := (181093281790194527671800788941649398648675316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209010241531578440967/50000000000000000000)
  centralHi := (83604096612631376387/20000000000000000000)
  directionLo := (52624469420648164173/12500000000000000000)
  directionHi := (84199151073037062677/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree072.table
  base := (486785333796151964556377103469730845149/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-5227599849192079537756193550099789000000000000)
      constant := (98349857672400165529320660453452026516594651984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree072.table
  base := (7788518892830106202878885643035286767619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-9893099127113987710587135411691000000000000)
      constant := (186329907255437307782482767792714963463727611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52624469420648164173/12500000000000000000)
  centralHi := (84199151073037062677/20000000000000000000)
  directionLo := (423950147789396209303/100000000000000000000)
  directionHi := (52993768473674526163/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree073.table
  base := (8612074822217727821168540347417429628139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-429313810574184125412454603542574760250000000000)
      constant := (8193441192912892994046436889767566249947568133859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree073.table
  base := (430601646197167847308141075819460671477/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-10030437304838282450499160831246000000000000)
      constant := (191641537700375363449918233710689652069592260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423950147789396209303/100000000000000000000)
  centralHi := (52993768473674526163/12500000000000000000)
  directionLo := (213442046927145318131/50000000000000000000)
  directionHi := (426884093854290636263/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree074.table
  base := (9457440153293671485957499390371771208297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-435192033363809808266657529527066611500000000000)
      constant := (8423750924095345230349171603275830868422479767857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree074.table
  base := (47287011759898496619558462272439330467/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-10167775482562577190411186250801000000000000)
      constant := (197028171915057959256994133007067449369784600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213442046927145318131/50000000000000000000)
  centralHi := (426884093854290636263/100000000000000000000)
  directionLo := (429798012281288645749/100000000000000000000)
  directionHi := (1719192049125154583/400000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree075.table
  base := (129058187031993494101089265072796005167/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-49007806239270610124540050612395384750000000000)
      constant := (961918624319260995016403104144991521025275676240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree075.table
  base := (2581155212911179636548387069025705022641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-10305113660286871930323211670356000000000000)
      constant := (202489808830510339104211966101220751595305316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429798012281288645749/100000000000000000000)
  centralHi := (1719192049125154583/400000000000000000)
  directionLo := (432692307692307692307/100000000000000000000)
  directionHi := (108173076923076923077/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree076.table
  base := (5606856808442250120594978372498463827639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-446948478943061173975063381496050314000000000000)
      constant := (8893991236454695583592527996060803572549070186718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree076.table
  base := (11213682831073112248077246484129017297743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-10442451838011166670235237089911000000000000)
      constant := (208026447501707266891898369911138803923318567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432692307692307692307/100000000000000000000)
  centralHi := (108173076923076923077/25000000000000000000)
  directionLo := (10889184281640504371/2500000000000000000)
  directionHi := (435567371265620174841/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree077.table
  base := (2424922226559872277083814994717864799831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-452826701732686856829266307480542165250000000000)
      constant := (9133921740751686342527093220039120868956787448555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree077.table
  base := (151557291796779286909653978831096437337/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-10579790015735461410147262509466000000000000)
      constant := (213638087092686433786475755214340298832796240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10889184281640504371/2500000000000000000)
  centralHi := (435567371265620174841/100000000000000000000)
  directionLo := (438423581352999912451/100000000000000000000)
  directionHi := (109605895338249978113/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree078.table
  base := (13057343098945305431429678000609283168069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3725738257238559867356997279210000000000000)
      linear := (-301581146957470440291564256058536500000000000)
      constant := (6165061867073997767994060596997896078413176509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree078.table
  base := (3264329502847676625280445136133636212369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (782553719226750654769375610000000000000)
      linear := (-63414959724613941716327147509000000000000)
      constant := (1297779448896577584526902910356534544849476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438423581352999912451/100000000000000000000)
  centralHi := (109605895338249978113/25000000000000000000)
  directionLo := (441261304060914071829/100000000000000000000)
  directionHi := (44126130406091407183/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree079.table
  base := (2802381121629746280978015619812744015841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-464583147311938222537672159449525867750000000000)
      constant := (9623403285364564976210942435671887158719444002605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree079.table
  base := (7005941478253898238122133183768598024461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-10854466371184050889971313348576000000000000)
      constant := (225086366158913542203157928824487161132267818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441261304060914071829/100000000000000000000)
  centralHi := (44126130406091407183/10000000000000000000)
  directionLo := (111020223449572012687/25000000000000000000)
  directionHi := (444080893798288050749/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree080.table
  base := (187353689973456895530523544322019911497/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-470461370101563905391875085434017719000000000000)
      constant := (9872954272312861889617477833099337350658176564560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree080.table
  base := (14988274743159110866464160597801032882891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-10991804548908345629883338768131000000000000)
      constant := (230923004398189294200836587172008374557208579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111020223449572012687/25000000000000000000)
  centralHi := (444080893798288050749/100000000000000000000)
  directionLo := (446882693793163486751/100000000000000000000)
  directionHi := (13965084181036358961/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree081.table
  base := (15986508797995323714094691625225600153241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-5880735714706044299334296437265550250000000000)
      constant := (125008790597927510549595099121847817605862398641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree081.table
  base := (499577822658536661208144319214392347649/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-11129142726632640369795364187686000000000000)
      constant := (236834641066528988247365144084359308816085792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446882693793163486751/100000000000000000000)
  centralHi := (13965084181036358961/3125000000000000000)
  directionLo := (8993340731607632101/2000000000000000000)
  directionHi := (449667036580381605051/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree082.table
  base := (8503271842450577752256721981807847219419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-482217815680815271100280937403001421500000000000)
      constant := (10381676563999438534630869389134841185111901039078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree082.table
  base := (17006527000062937398034919994530808099427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-11266480904356935109707389607241000000000000)
      constant := (242821275707263013576382616012652706568803163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8993340731607632101/2000000000000000000)
  centralHi := (449667036580381605051/100000000000000000000)
  directionLo := (113108561115563379333/25000000000000000000)
  directionHi := (452434244462253517333/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree083.table
  base := (9024198720605724946938518039521561818817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-488096038470440953954483863387493272750000000000)
      constant := (10640847831509362283184637662390228985041639995954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree083.table
  base := (56401194906177345762760567783595198459/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-11403819082081229849619415026796000000000000)
      constant := (248882907915103740840943880319304203332662720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113108561115563379333/25000000000000000000)
  centralHi := (452434244462253517333/100000000000000000000)
  directionLo := (455184629944024039767/100000000000000000000)
  directionHi := (56898078743003004971/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree084.table
  base := (9556033960158254211450480001783733822723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-54886029028896292978742976596887236000000000000)
      constant := (1211469536157474028263318867843516384949734660614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree084.table
  base := (19112054305480601740570427523637094504827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-11541157259805524589531440446351000000000000)
      constant := (255019537330193722155645124697513668971315763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455184629944024039767/100000000000000000000)
  centralHi := (56898078743003004971/12500000000000000000)
  directionLo := (457918496145794525279/100000000000000000000)
  directionHi := (2861990600911215783/625000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree085.table
  base := (4039510643036257359029126051432274469257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-499852484049692319662889715356476975250000000000)
      constant := (11168810531913392408579740207837602659318610748085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree085.table
  base := (20197540915065220623769721754245030922463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-11678495437529819329443465865906000000000000)
      constant := (261231163632867890879716598407399285225896247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457918496145794525279/100000000000000000000)
  centralHi := (2861990600911215783/625000000000000000)
  directionLo := (11515903429811042307/2500000000000000000)
  directionHi := (460636137192441692281/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree086.table
  base := (21304851630867269610630215105767290760321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-505730706839318002517092641340968826500000000000)
      constant := (11437601938723875690377080260761719789993590075401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree086.table
  base := (21304840517750881113723105144092936441441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-11815833615254114069355491285461000000000000)
      constant := (267517786539040673288745372537657706258603529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11515903429811042307/2500000000000000000)
  centralHi := (460636137192441692281/100000000000000000000)
  directionLo := (463337838582952227129/100000000000000000000)
  directionHi := (46333783858295222713/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree087.table
  base := (22433961660313285272588001707143992336773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-56845436625438187263477285258384519750000000000)
      constant := (1301066670548373473311796017431605887569161086757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree087.table
  base := (4486790323806254804522864619163493318299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-11953171792978408809267516705016000000000000)
      constant := (273879405796140503129990500061334526853962655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463337838582952227129/100000000000000000000)
  centralHi := (46333783858295222713/10000000000000000000)
  directionLo := (466023877540485925781/100000000000000000000)
  directionHi := (233011938770242962891/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree088.table
  base := (4716976392594726956134857155676942340079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-517487152418569368225498493309952529000000000000)
      constant := (11984804810840312907924276726690514287468888084995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree088.table
  base := (23584872889657071206663038442564023326873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-12090509970702703549179542124571000000000000)
      constant := (280316021179524243947153103997231319942241537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466023877540485925781/100000000000000000000)
  centralHi := (233011938770242962891/50000000000000000000)
  directionLo := (58586815418047791061/12500000000000000000)
  directionHi := (468694523344382328489/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree089.table
  base := (12378805672981730377520727096499288499443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-523365375208195051079701419294444380250000000000)
      constant := (12263216257800477604827541696829069442841032490166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree089.table
  base := (24757603146911090663119171577871924030553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-12227848148426998289091567544126000000000000)
      constant := (286827632489312691981768420891856230161163457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58586815418047791061/12500000000000000000)
  centralHi := (468694523344382328489/100000000000000000000)
  directionLo := (942700075290472607/200000000000000000)
  directionHi := (471350037645236303501/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree090.table
  base := (25952148747405948988310353321595907947261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-6533871580220009060912399324431311500000000000)
      constant := (154874498371929562667811023043170519047643080661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree090.table
  base := (25952141338071407099172909623003156184663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-12365186326151293029003592963681000000000000)
      constant := (293414239547595841859351592368702533395208047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (942700075290472607/200000000000000000)
  centralHi := (471350037645236303501/100000000000000000000)
  directionLo := (236995337382043029861/50000000000000000000)
  directionHi := (473990674764086059723/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree091.table
  base := (849015413178583997850348998014214738063/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (33531644315147038806212975512890000000000000)
      linear := (-3166401306434594182178149534103124750000000000)
      constant := (75915142810475253187145043223956708645522867584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree091.table
  base := (27168486525797281616322607216864094769487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (782553719226750654769375610000000000000)
      linear := (-73979434934175075555713718244000000000000)
      constant := (1775596699384397092935241658945239094769487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236995337382043029861/50000000000000000000)
  centralHi := (473990674764086059723/100000000000000000000)
  directionLo := (476616681976681905629/100000000000000000000)
  directionHi := (47661668197668190563/10000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree092.table
  base := (28406643926578129414107291000947297840383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1670058)
      previous := (835029)
      next := (835029)
      square := (10712377862494989713137982725290000000000000)
      linear := (-1022684392395221360382438936196446000000000000)
      constant := (24797146601574601456107734867910161435137002887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree092.table
  base := (14203318937603111273597556819067959823879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-12639862681599882508827643802791000000000000)
      constant := (306812440293319351430095102399081970420471102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476616681976681905629/100000000000000000000)
  centralHi := (47661668197668190563/10000000000000000000)
  directionLo := (479228299783735087649/100000000000000000000)
  directionHi := (9584565995674701753/2000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree093.table
  base := (29666600111442297945356089364997311115599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-60764251818521975832945902581379087250000000000)
      constant := (1489880957164345707561770600064215817350973495791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree093.table
  base := (29666594642439535457519578427719244140943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-12777200859324177248739669222346000000000000)
      constant := (313624033713952450672077604753124427259819367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479228299783735087649/100000000000000000000)
  centralHi := (9584565995674701753/2000000000000000000)
  directionLo := (481825762167982666337/100000000000000000000)
  directionHi := (240912881083991333169/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree094.table
  base := (30948361107313288143199305887529674507939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-552756489156323465350716049216903636500000000000)
      constant := (13703373316864252727014543105528873984166674617659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree094.table
  base := (30948356164538973321986537373568227969223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-12914539037048471988651694641901000000000000)
      constant := (320510622345822462684726047972037030526798687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481825762167982666337/100000000000000000000)
  centralHi := (240912881083991333169/50000000000000000000)
  directionLo := (242204648419423055797/50000000000000000000)
  directionHi := (96881859367769222319/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree095.table
  base := (8062981579430796850442090907408417034071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-558634711945949148204918975201395487750000000000)
      constant := (14001024655069077190911757071577110144495768496604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree095.table
  base := (32251921850479072765731711591626359885401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-13051877214772766728563720061456000000000000)
      constant := (327472206089046084157688368924414229820632769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242204648419423055797/50000000000000000000)
  centralHi := (96881859367769222319/20000000000000000000)
  directionLo := (60872390683175957391/12500000000000000000)
  directionHi := (486979125465407659129/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree096.table
  base := (6715459042144461665422337441045010025403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-62723659415063870117680211242876371000000000000)
      constant := (1589098069471275689503148605627139348357647412135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree096.table
  base := (8394322793304725396978129881948999924989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-13189215392497061468475745481011000000000000)
      constant := (334508784854553397549022171327613523949292564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60872390683175957391/12500000000000000000)
  centralHi := (486979125465407659129/100000000000000000000)
  directionLo := (244767731949189527677/50000000000000000000)
  directionHi := (97907092779675811071/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree097.table
  base := (34924467311777395258398037963865530726857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-570391157525200513913324827170379190250000000000)
      constant := (14605947223945141216128232383836691439415013655217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree097.table
  base := (34924463662653627237912322697724950326963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-13326553570221356208387770900566000000000000)
      constant := (341620358562896686157673243277779391605256747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244767731949189527677/50000000000000000000)
  centralHi := (97907092779675811071/20000000000000000000)
  directionLo := (492078522381691753943/100000000000000000000)
  directionHi := (61509815297711469243/12500000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree098.table
  base := (36293442197470110586022205568733459576961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-576269380314826196767527753154871041500000000000)
      constant := (14913218448113881375859900322999324475622081119241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree098.table
  base := (3629343889936087322147984819746102147333/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-13463891747945650948299796320121000000000000)
      constant := (348806927143193568356113119654143912628992770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492078522381691753943/100000000000000000000)
  centralHi := (61509815297711469243/12500000000000000000)
  directionLo := (6182606321928694719/1250000000000000000)
  directionHi := (494608505754295577521/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree099.table
  base := (37684219489902893304477731216294451494629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-7187007445733973822490502211597072750000000000)
      constant := (187946867839643996009328708041099706922133827229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree099.table
  base := (37684216509049542925022709526698847937603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-13601229925669945688211821739676000000000000)
      constant := (356068490532188848816644687138155480301454907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6182606321928694719/1250000000000000000)
  centralHi := (494608505754295577521/100000000000000000000)
  directionLo := (6214070170533925233/1250000000000000000)
  directionHi := (497125613642714018641/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree100.table
  base := (39096798851730458945364086015582045890329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-588025825894077562475933605123854744000000000000)
      constant := (15537380762194108650897889938472062098630945537249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree100.table
  base := (78193592315259803037622612405535234893/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-13738568103394240428123847159231000000000000)
      constant := (363405048673421362353043643248242727348458500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6214070170533925233/1250000000000000000)
  centralHi := (497125613642714018641/100000000000000000000)
  directionLo := (99926008128973690011/20000000000000000000)
  directionHi := (62453755080608556257/12500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree101.table
  base := (20265589990872493933194810285042240175919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-593904048683703245330136531108346595250000000000)
      constant := (15854271847481525595295612308864780595651770692078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree101.table
  base := (8106235509366685305538449263929295140637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-13875906281118535168035872578786000000000000)
      constant := (370816601516483728667009064752288129393838265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/20000000000000000000)
  centralHi := (62453755080608556257/12500000000000000000)
  directionLo := (502121976505650296559/100000000000000000000)
  directionHi := (6276524706320628707/1250000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree102.table
  base := (41987362610951610198548399732123313604251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-66642474608147658687148828565870938500000000000)
      constant := (1797152172102832585632768166027565125017052792859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree102.table
  base := (41987360410319447794511220902358588045889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-14013244458842829907947897998341000000000000)
      constant := (378303149016364374501981873433520601379755241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502121976505650296559/100000000000000000000)
  centralHi := (6276524706320628707/1250000000000000000)
  directionLo := (20184064251387578553/4000000000000000000)
  directionHi := (252300803142344731913/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree103.table
  base := (10866336624769574558123665932497015244971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-605660494262954611038542383077330297750000000000)
      constant := (16497673864786086353607092652804572874914233868204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree103.table
  base := (43465344510213054756989422424098186363821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-14150582636567124647859923417896000000000000)
      constant := (385864691132862439972936950819909968495485749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20184064251387578553/4000000000000000000)
  centralHi := (252300803142344731913/50000000000000000000)
  directionLo := (507069110516738819017/100000000000000000000)
  directionHi := (253534555258369409509/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree104.table
  base := (44965131431470857063128351148889560580877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (33531644315147038806212975512890000000000000)
      linear := (-3618572290251954401732220763679421000000000000)
      constant := (99551389310703494497376159092900662781329998573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree104.table
  base := (22482564817012644456196059160882632518677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (782553719226750654769375610000000000000)
      linear := (-84543910143736209395100288979000000000000)
      constant := (2328409632130575686940308444427765265037354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507069110516738819017/100000000000000000000)
  centralHi := (253534555258369409509/50000000000000000000)
  directionLo := (254762332682534043887/50000000000000000000)
  directionHi := (20380986614602723511/4000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree105.table
  base := (46486717216329480031184059244277558162613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-68601882204689552971883137227368222250000000000)
      constant := (1905989148189443473812956034222555001209724383317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree105.table
  base := (46486715591912379557931941936008736033701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-14425258992015714127683974257006000000000000)
      constant := (401212759075895330613136337333237351389695469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254762332682534043887/50000000000000000000)
  centralHi := (20380986614602723511/4000000000000000000)
  directionLo := (511968442768236003683/100000000000000000000)
  directionHi := (127992110692059000921/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree106.table
  base := (12007525920562102320191046110266675249493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-623295162631831659601151161030805851500000000000)
      constant := (17486826484133156897583109682478409222290745276532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree106.table
  base := (48030102214235823202459385040314194228077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-14562597169740008867595999676561000000000000)
      constant := (408999284841677651443605314604464098824545013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511968442768236003683/100000000000000000000)
  centralHi := (127992110692059000921/25000000000000000000)
  directionLo := (257200305290293382931/50000000000000000000)
  directionHi := (514400610580586765863/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree107.table
  base := (9919058135204940480627008114807284601847/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-629173385421457342455354087015297702750000000000)
      constant := (17822957243683971273259147787701047054193400577035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree107.table
  base := (24797644674694769889785262830473173792927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-14699935347464303607508025096116000000000000)
      constant := (416860805101792826053096796108411307742009326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257200305290293382931/50000000000000000000)
  centralHi := (514400610580586765863/100000000000000000000)
  directionLo := (258410666353397844009/50000000000000000000)
  directionHi := (516821332706795688019/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree108.table
  base := (25591139030353015384462134985840767682341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-7840143311247938584068605098762834000000000000)
      constant := (224225859399576502539127933995895054818137935482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree108.table
  base := (25591138430932119321769656906270224321089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-14837273525188598347420050515671000000000000)
      constant := (424797319833339784322483079397552335820528082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258410666353397844009/50000000000000000000)
  centralHi := (516821332706795688019/100000000000000000000)
  directionLo := (519230769230769230769/100000000000000000000)
  directionHi := (51923076923076923077/10000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree109.table
  base := (52791065713850890771815962854488224906851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-640929831000708708163759938984281405250000000000)
      constant := (18504838586291675372837186139711702913300750786331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree109.table
  base := (1319776615763064023446129770122062185419/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-14974611702912893087332075935226000000000000)
      constant := (432808829015846312605012190053241015373432440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519230769230769230769/100000000000000000000)
  centralHi := (51923076923076923077/10000000000000000000)
  directionLo := (130407269134796570481/25000000000000000000)
  directionHi := (20865163061567451277/4000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree110.table
  base := (54421653525977654099901761702311649313783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-646808053790334391017962864968773256500000000000)
      constant := (18850589167669098143492871801110321480365672632623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree110.table
  base := (54421652547061590250985402642690412533727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-15111949880637187827244101354781000000000000)
      constant := (440895332631009218027140162650274679718199863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130407269134796570481/25000000000000000000)
  centralHi := (20865163061567451277/4000000000000000000)
  directionLo := (524016407439950480553/100000000000000000000)
  directionHi := (262008203719975240277/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree111.table
  base := (7009255174897696006816675517657484567897/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-72520697397773341541351754550362789750000000000)
      constant := (2133282928309887734573273280022200202169590798184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree111.table
  base := (11214808102928398194001706129603774209799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-15249288058361482567156126774336000000000000)
      constant := (449056830662462652870278207432080564207280155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524016407439950480553/100000000000000000000)
  centralHi := (262008203719975240277/50000000000000000000)
  directionLo := (263196455637903736543/50000000000000000000)
  directionHi := (526392911275807473087/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree112.table
  base := (28874114622950593030347682524280772876199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-658564499369585756726368716937756959000000000000)
      constant := (19551710147017275224131459297098572453896620821438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree112.table
  base := (11549645689333077473753715812604398203559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-15386626236085777307068152193891000000000000)
      constant := (457293323095571491636707651115582716482007355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263196455637903736543/50000000000000000000)
  centralHi := (526392911275807473087/100000000000000000000)
  directionLo := (264379367016683077303/50000000000000000000)
  directionHi := (528758734033366154607/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree113.table
  base := (59444216987817800412906733463868046480309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-664442722159211439580571642922248810250000000000)
      constant := (19907080543786811548615077519224577167445836997629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree113.table
  base := (59444216265683674560844151571484173650507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-15523964413810072046980177613446000000000000)
      constant := (465604809917247004600623277723340700346935683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264379367016683077303/50000000000000000000)
  centralHi := (528758734033366154607/100000000000000000000)
  directionLo := (531114018447749104723/100000000000000000000)
  directionHi := (132778504611937276181/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree114.table
  base := (61162004554873297630089871415973133092767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-74480104994315235826086063211860073500000000000)
      constant := (2251739727176697120771249623520494153925888163103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree114.table
  base := (489296031219406307733026699162988028437/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-15661302591534366786892203033001000000000000)
      constant := (473991291115782381932571519333867122100731625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531114018447749104723/100000000000000000000)
  centralHi := (132778504611937276181/25000000000000000000)
  directionLo := (266729452051542250251/50000000000000000000)
  directionHi := (533458904103084500503/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree115.table
  base := (62901591884393490952477423822322573759949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1670058)
      previous := (835029)
      next := (835029)
      square := (10712377862494989713137982725290000000000000)
      linear := (-1278259296291990180130392239870004750000000000)
      constant := (38993272493334232337426577898350875626262441861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree115.table
  base := (62901591294929085120765726434251255135761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-15798640769258661526804228452556000000000000)
      constant := (482452766680705936802407311640187837117943609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266729452051542250251/50000000000000000000)
  centralHi := (533458904103084500503/100000000000000000000)
  directionLo := (535793527529039710701/100000000000000000000)
  directionHi := (267896763764519855351/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree116.table
  base := (64662978920305430211089106528446095428571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-682077390528088488143180420875724364000000000000)
      constant := (20992431356531364804024699291774877082945183753651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree116.table
  base := (16165744596940978884374659712351517683593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-15935978946982956266716253872111000000000000)
      constant := (490989236602650058531537606749560625954108868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535793527529039710701/100000000000000000000)
  centralHi := (267896763764519855351/50000000000000000000)
  directionLo := (538118022293585483397/100000000000000000000)
  directionHi := (269059011146792741699/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree117.table
  base := (66446165612438469033268607900206701595693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (413970917470951096372999697690000000000000)
      linear := (-50256089803324871867731999916737250000000000)
      constant := (1560422833435578347363142359711999196706621597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree117.table
  base := (66446165131341253323006101722238866012823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (782553719226750654769375610000000000000)
      linear := (-95108385353297343234486859714000000000000)
      constant := (2956217164930379891475779054667113866012823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538118022293585483397/100000000000000000000)
  centralHi := (269059011146792741699/50000000000000000000)
  directionLo := (108086503818433815101/20000000000000000000)
  directionHi := (270216259546084537753/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree118.table
  base := (13650230383180000564291294501460336620591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-693833836107339853851586272844708066500000000000)
      constant := (21732031579753521542352989676326769075989319676355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree118.table
  base := (17062787870323589466007976452366695603981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-16210655302431545746540304711221000000000000)
      constant := (508287159484960387022374172745617886228291156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108086503818433815101/20000000000000000000)
  centralHi := (270216259546084537753/50000000000000000000)
  directionLo := (542737145833464784879/100000000000000000000)
  directionHi := (6784214322918309811/1250000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree119.table
  base := (70077937790517795430609966078538795484447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-699712058896965536705789198829199917750000000000)
      constant := (22106641594802126955149660830049625814115071246007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree119.table
  base := (35038968698963226700912577874396230971159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-16347993480155840486452330130776000000000000)
      constant := (517048612431119859517211242953959301068251742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542737145833464784879/100000000000000000000)
  centralHi := (6784214322918309811/1250000000000000000)
  directionLo := (545032027721861085031/100000000000000000000)
  directionHi := (68129003465232635629/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree120.table
  base := (71926523200341703127367754232160426180933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-78398920187399024395554680534854641000000000000)
      constant := (2498273134642790661405740450467331413349014320197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree120.table
  base := (287706091382869154734253285549293491549/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-16485331657880135226364355550331000000000000)
      constant := (525885059705709696682190863267927650017945250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545032027721861085031/100000000000000000000)
  centralHi := (68129003465232635629/12500000000000000000)
  directionLo := (17103665229276090137/3125000000000000000)
  directionHi := (109463457467366976877/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree121.table
  base := (18449227028299598636967125600936962800983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-711468504476216902414195050798183620250000000000)
      constant := (22865481430469505967080893407912958328260663203292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree121.table
  base := (18449226948220556599053361379064353867871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-16622669835604429966276380969886000000000000)
      constant := (534796501303358294811410463919235378214680796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17103665229276090137/3125000000000000000)
  centralHi := (109463457467366976877/20000000000000000000)
  directionLo := (549593044709355295061/100000000000000000000)
  directionHi := (274796522354677647531/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree122.table
  base := (75689092500293366674205148581494073831989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-717346727265842585268397976782675471500000000000)
      constant := (23249711250646782151928732241846230496048195535709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree122.table
  base := (75689092210978207852162535421713433543089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-16760008013328724706188406389441000000000000)
      constant := (543782937219258776986663449139236570268782041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549593044709355295061/100000000000000000000)
  centralHi := (274796522354677647531/50000000000000000000)
  directionLo := (551859417395451662757/100000000000000000000)
  directionHi := (275929708697725831379/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree123.table
  base := (77603076335855179605093512204395137371853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-80358327783940918680288989196351924750000000000)
      constant := (2626349741347813457200821031874746636687191770477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree123.table
  base := (15520615214910311326427942990721738989347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-16897346191053019446100431808996000000000000)
      constant := (552844367449109471893093040858567244445998215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551859417395451662757/100000000000000000000)
  centralHi := (275929708697725831379/50000000000000000000)
  directionLo := (554116520547073444023/100000000000000000000)
  directionHi := (69264565068384180503/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree124.table
  base := (79538859596817386154733559451454640464529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-729103172845093950976803828751659174000000000000)
      constant := (24027790694753087616683390128278323189160717927449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree124.table
  base := (79538859360823134093374488505023169150101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-17034684368777314186012457228551000000000000)
      constant := (561980791989060705100071025319657915586367069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554116520547073444023/100000000000000000000)
  centralHi := (69264565068384180503/12500000000000000000)
  directionLo := (69545558372545348527/12500000000000000000)
  directionHi := (556364466980362788217/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree125.table
  base := (40748221131267062023055402709288675143599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-734981395634719633831006754736151025250000000000)
      constant := (24421640318365575038149117636905248422299151360238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree125.table
  base := (81496442049406847741105661988390310988807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-17172022546501608925924482648106000000000000)
      constant := (571192210835667226975982760721709837557108383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69545558372545348527/12500000000000000000)
  centralHi := (556364466980362788217/100000000000000000000)
  directionLo := (558603367241454358439/100000000000000000000)
  directionHi := (13965084181036358961/2500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree126.table
  base := (83475824314525775696775104869384282993699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (69961085052590735287036948909610000000000000)
      linear := (-9146415042275868107224810873094356500000000000)
      constant := (306403661022641525673999915463913784065169684299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree126.table
  base := (4173791206102897371057126453275487067537/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-17309360724225903665836508067661000000000000)
      constant := (580478623985845674744770017693567146288275060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558603367241454358439/100000000000000000000)
  centralHi := (13965084181036358961/2500000000000000000)
  directionLo := (22433333186796439261/4000000000000000000)
  directionHi := (280416664834955490763/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree127.table
  base := (42738502868125744761598715145199478434077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-746737841213970999539412606705134727750000000000)
      constant := (25218959368038472978552071309606310263807119196074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree127.table
  base := (85477005562447930277862835490654105113779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-17446698901950198405748533487216000000000000)
      constant := (589840031436836531423832635267701918764228651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22433333186796439261/4000000000000000000)
  centralHi := (280416664834955490763/50000000000000000000)
  directionLo := (11261089209197962521/2000000000000000000)
  directionHi := (563054460459898126051/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree128.table
  base := (87499986512905702783557698244603192268607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (883460682)
      previous := (441730341)
      next := (441730341)
      square := (5666847889259849558249992861678410000000000000)
      linear := (-752616064003596682393615532689626579000000000000)
      constant := (25622428793871889033734154068365547841352464486967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree128.table
  base := (87499986355963218870484700781494851651057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-17584037079674493145660558906771000000000000)
      constant := (599276433186170102425678475642600629929028633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell099.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11261089209197962521/2000000000000000000)
  centralHi := (563054460459898126051/100000000000000000000)
  directionLo := (565266863719194945737/100000000000000000000)
  directionHi := (282633431859597472869/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree129.table
  base := (89544766631236114068938071891732052834971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (629649765473316617583332540186490000000000000)
      linear := (-84277142977024707249757606519346492250000000000)
      constant := (2892122757804249495142365520312761185588555681339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree129.table
  base := (4477238324476254127521852809736406580719/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (132251578549320860656024478090000000000000)
      linear := (-17721375257398787885572584326326000000000000)
      constant := (608787829231636082270699028200644929242830220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell099.Kernel129
