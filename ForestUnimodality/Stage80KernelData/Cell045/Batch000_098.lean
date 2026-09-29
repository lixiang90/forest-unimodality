import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell045.Parameters
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch000_049
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch050_099
import ForestUnimodality.BinomialMassData.Q47_97.Batch000_049
import ForestUnimodality.BinomialMassData.Q47_97.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree000.table
  base := (79763867931187922490892107/2000000000000000000000000)
  polynomial :=
    { denominator := 250000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (30573320893639906181693532500000000000)
      linear := (1054312292143938772220890250000000000)
      constant := (9970483491398490311361513375000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree000.table
  base := (79763867931187922490892107/2000000000000000000000000)
  polynomial :=
    { denominator := 250000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (30573320893639906181693532500000000000)
      linear := (1054312292143938772220890250000000000)
      constant := (9970483491398490311361513375000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree001.table
  base := (115104785537904477700505601163265767261553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4365000000000000000000000000000000000000000
      center := (34920)
      previous := (17460)
      next := (17460)
      square := (533810182802952761932369077450000000000000)
      linear := (-497459172482664671029010941799062500000000)
      constant := (100602214964986781220822485223287364916992019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree001.table
  base := (229740419236977579009541480963330825760219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-110864954866567564806950628030000000000000)
      constant := (22310688647889574168417402405873090098741243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49971746941548789863/100000000000000000000)
  directionHi := (6246468367693598733/12500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree002.table
  base := (68465141093492931723375848974616540782963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4365000000000000000000000000000000000000000
      center := (34920)
      previous := (17460)
      next := (17460)
      square := (533810182802952761932369077450000000000000)
      linear := (-1013326637586162513020998627363125000000000)
      constant := (60250806479298399344527527394665171744151699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree002.table
  base := (136411057030365081360632841390680366059129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-225820641426653612050118310230000000000000)
      constant := (13339308673774870119732451171955995507735513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49971746941548789863/100000000000000000000)
  centralHi := (6246468367693598733/12500000000000000000)
  directionLo := (70670722260214531273/100000000000000000000)
  directionHi := (35335361130107265637/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree003.table
  base := (42262999882575454371909968617916131332459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-169910455854406706112554034769687500000000)
      constant := (4221178026704118327988372233294058586904773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree003.table
  base := (84087818798259185082793663812329867367309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-340776327986739659293285992430000000000000)
      constant := (8401222903211265622808545803685997134628973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70670722260214531273/100000000000000000000)
  centralHi := (35335361130107265637/50000000000000000000)
  directionLo := (17310720929147431093/20000000000000000000)
  directionHi := (43276802322868577733/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree004.table
  base := (54390442630222398483028438603295552761693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-4090123135586316394009947996982500000000000)
      constant := (51399921025994238263431235254474595685957989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree004.table
  base := (422291573277950354390101710121443762191/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-56966501818353213317056709328750000000000)
      constant := (710105646196722866334858269473480718920432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17310720929147431093/20000000000000000000)
  centralHi := (43276802322868577733/50000000000000000000)
  directionLo := (49971746941548789863/50000000000000000000)
  directionHi := (99943493883097579727/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree005.table
  base := (7294620422272484605345700833985479962319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1746000000000000000000000000000000000000000
      center := (13968)
      previous := (6984)
      next := (6984)
      square := (213524073121181104772947630980000000000000)
      linear := (-1024371613158662415598784673622125000000000)
      constant := (7596733704983125730861869340830949983666987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree005.table
  base := (36220849145177462759735867122438812096791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-570687701106911753779621356830000000000000)
      constant := (4199764056835551097826853395026564773388727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49971746941548789863/50000000000000000000)
  centralHi := (99943493883097579727/100000000000000000000)
  directionLo := (111740223115720304029/100000000000000000000)
  directionHi := (11174022311572030403/10000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree006.table
  base := (6331002679057366554678278628579152788883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-170933138777786326721608298312187500000000)
      constant := (860406259906226596446008516484487390834151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree006.table
  base := (2513361374187249329877340846435751680793/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 97000000000000000000000000000000000000000
      center := (776)
      previous := (388)
      next := (388)
      square := (11862448506732283598497090610000000000000)
      linear := (-68564338766699780102278903903000000000000)
      constant := (342867109473751415844191391862267913036921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111740223115720304029/100000000000000000000)
  centralHi := (11174022311572030403/10000000000000000000)
  directionLo := (1912582524410631439/1562500000000000000)
  directionHi := (122405281562280412097/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree007.table
  base := (4497405846167668508859015022844569643717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1091250000000000000000000000000000000000000
      center := (8730)
      previous := (4365)
      next := (4365)
      square := (133452545700738190483092269362500000000000)
      linear := (-898165990775912930745234263795859375000000)
      constant := (3474293335450797894264534248684482408271533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree007.table
  base := (55753706147106752466416966226568356651/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 24250000000000000000000000000000000000000
      center := (194)
      previous := (97)
      next := (97)
      square := (2965612126683070899624272652500000000000)
      linear := (-20014976855677096206648918030750000000000)
      constant := (77034366265714505552855074872067044761176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1912582524410631439/1562500000000000000)
  centralHi := (122405281562280412097/100000000000000000000)
  directionLo := (66106407493395327897/50000000000000000000)
  directionHi := (26442562997358131159/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree008.table
  base := (12861273931044417527033093937433770498433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-8217062856414299129945849481495000000000000)
      constant := (27038466925797163627257761292966244145132009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree008.table
  base := (12740200464991707177398493944566578960239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-915554760787169895509124403430000000000000)
      constant := (3002348284997045757627309393662958159143183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66106407493395327897/50000000000000000000)
  centralHi := (26442562997358131159/20000000000000000000)
  directionLo := (70670722260214531273/50000000000000000000)
  directionHi := (141341444520429062547/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree009.table
  base := (9057111488297997788486524102725658897729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-1027644198513477201547758316958125000000000)
      constant := (3104125586251054749711147047974940670892213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree009.table
  base := (2238395720454589335174893182495891606301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-257627611836813985688073021407500000000000)
      constant := (776628946380913394524464301469601485811197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70670722260214531273/50000000000000000000)
  centralHi := (141341444520429062547/100000000000000000000)
  directionLo := (14991524082464636959/10000000000000000000)
  directionHi := (149915240824646369591/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree010.table
  base := (6088803593903080600635636415540724437579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-10280532716828290497913800223751250000000000)
      constant := (30064022495206134741216656933994884465256467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree010.table
  base := (5996582571927573663977655908290060361441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-1145466133907341989995459767830000000000000)
      constant := (3346856339582629534853482496404135855059777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14991524082464636959/10000000000000000000)
  centralHi := (149915240824646369591/100000000000000000000)
  directionLo := (158024538992847273353/100000000000000000000)
  directionHi := (79012269496423636677/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree011.table
  base := (3681566065853017777792319973765102167611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-11312267647035286181897775594879375000000000)
      constant := (33179256991745285742601040982082095325136903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree011.table
  base := (143874633586905090172520829180889910189/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 194000000000000000000000000000000000000000
      center := (1552)
      previous := (776)
      next := (776)
      square := (23724897013464567196994181220000000000000)
      linear := (-252084364093485607447725490006000000000000)
      constant := (739390715739248185056194431698731606441665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158024538992847273353/100000000000000000000)
  centralHi := (79012269496423636677/50000000000000000000)
  directionLo := (82868767361853674389/50000000000000000000)
  directionHi := (165737534723707348779/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree012.table
  base := (20961752539561042009103115774183914171/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24250000000000000000000000000000000000000
      center := (194)
      previous := (97)
      next := (97)
      square := (2965612126683070899624272652500000000000)
      linear := (-34288896047895227405227086016687500000000)
      constant := (103179164777552364969853187225099882474174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree012.table
  base := (1597555500228402194173170601261022654057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-1375377507027514084481795132230000000000000)
      constant := (4141590415936451505379674022682319197443529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82868767361853674389/50000000000000000000)
  centralHi := (165737534723707348779/100000000000000000000)
  directionLo := (173107209291474310931/100000000000000000000)
  directionHi := (43276802322868577733/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree013.table
  base := (-19773272010970709601024998682467207277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-13375737507449277549865726337135625000000000)
      constant := (41877077010164088925309171970523414135859679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree013.table
  base := (-47535641823142743041307953784150699073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-745166596793800065862481407215000000000000)
      constant := (2335837868045433215047219055077937382189919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173107209291474310931/100000000000000000000)
  centralHi := (43276802322868577733/25000000000000000000)
  directionLo := (36035139184452989061/20000000000000000000)
  directionHi := (90087847961132472653/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree014.table
  base := (-1467975401048061077208578992468054043903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-14407472437656273233849701708263750000000000)
      constant := (47325132953361918320863699181579314600922681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree014.table
  base := (-769918173358802819376245662914621702687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-802644440073843089484065248315000000000000)
      constant := (2640751910593583611876171812807281694839361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36035139184452989061/20000000000000000000)
  centralHi := (90087847961132472653/50000000000000000000)
  directionLo := (186977156073844142939/100000000000000000000)
  directionHi := (9348857803692207147/5000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree015.table
  base := (-338401792205252885351249446338974218659/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-428866871329535247717602141094218750000000)
      constant := (1484837266981556942315722922361880847283279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree015.table
  base := (-2775958832787200747759784875033085845703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-1720244566707772226211298178830000000000000)
      constant := (5967270414276594565412827634571790672966809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186977156073844142939/100000000000000000000)
  centralHi := (9348857803692207147/5000000000000000000)
  directionLo := (48384935921377470671/25000000000000000000)
  directionHi := (38707948737101976537/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree016.table
  base := (-376559873974429345458162083301907188457/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 873000000000000000000000000000000000000000
      center := (6984)
      previous := (3492)
      next := (3492)
      square := (106762036560590552386473815490000000000000)
      linear := (-1647094229807026460181765245052000000000000)
      constant := (6023956412569487946911819989591310024477039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree016.table
  base := (-3831370763568476488961272461879824612001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-1835200253267858273454465861030000000000000)
      constant := (6726266109252948104517782874077657012635903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48384935921377470671/25000000000000000000)
  centralHi := (38707948737101976537/20000000000000000000)
  directionLo := (199886987766195159453/100000000000000000000)
  directionHi := (99943493883097579727/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree017.table
  base := (-4664408778308707733941622564615910592637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-17502677228277260285801627821648125000000000)
      constant := (67662822907195708530462162777733166497940399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree017.table
  base := (-4727265574028580806009455122425127724143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-1950155939827944320697633543230000000000000)
      constant := (7556435142924414490532916743634762610758129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199886987766195159453/100000000000000000000)
  centralHi := (99943493883097579727/50000000000000000000)
  directionLo := (206038790936641938389/100000000000000000000)
  directionHi := (20603879093664193839/10000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree018.table
  base := (-5420648224139527125580351903964878198469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-2059379128720472885531733688086250000000000)
      constant := (8412119295991824119522581922956676345998507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree018.table
  base := (-2740305751253348415835261985663827397773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-1032555813194015183970400612715000000000000)
      constant := (4228065798086046479789954352560608742416019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206038790936641938389/100000000000000000000)
  centralHi := (20603879093664193839/10000000000000000000)
  directionLo := (10600608339032179691/5000000000000000000)
  directionHi := (212012166780643593821/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree019.table
  base := (-6048479141512899187775238536894608872849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-19566147088691251653769578563904375000000000)
      constant := (84365952913773928286465227366815464461815323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree019.table
  base := (-244222516828093342838700143581739436299/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 194000000000000000000000000000000000000000
      center := (1552)
      previous := (776)
      next := (776)
      square := (23724897013464567196994181220000000000000)
      linear := (-436013462589623283036793781526000000000000)
      constant := (1884796498988226227634305074836856373394985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10600608339032179691/5000000000000000000)
  centralHi := (212012166780643593821/100000000000000000000)
  directionLo := (13613862184399931553/6250000000000000000)
  directionHi := (217821794950398904849/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree020.table
  base := (-3280023960766553953655521511292935025481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4365000000000000000000000000000000000000000
      center := (34920)
      previous := (17460)
      next := (17460)
      square := (533810182802952761932369077450000000000000)
      linear := (-10298941009449123668876776967516250000000000)
      constant := (46811428428652101121142518495092244285255087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree020.table
  base := (-6614272599815278281195896661965120430997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-2295022999508202462427136589830000000000000)
      constant := (10458809020425149662350102990389383318193291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13613862184399931553/6250000000000000000)
  centralHi := (217821794950398904849/100000000000000000000)
  directionLo := (223480446231440608059/100000000000000000000)
  directionHi := (11174022311572030403/5000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree021.table
  base := (-696597777132331952694533938332376860267/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 97000000000000000000000000000000000000000
      center := (776)
      previous := (388)
      next := (388)
      square := (11862448506732283598497090610000000000000)
      linear := (-240329077212280478019305881179562500000000)
      constant := (1149672349274430164591503378391802901585351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree021.table
  base := (-3508688150337601519481262524327933688117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-1204989343034144254835152136015000000000000)
      constant := (5779789751911835170342389916655190432252651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223480446231440608059/100000000000000000000)
  centralHi := (11174022311572030403/5000000000000000000)
  directionLo := (57249828242206329517/25000000000000000000)
  directionHi := (228999312968825318069/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree022.table
  base := (-1818919160460916704392385199461521348469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2182500000000000000000000000000000000000000
      center := (17460)
      previous := (8730)
      next := (8730)
      square := (266905091401476380966184538725000000000000)
      linear := (-5665337969828059676430376169322187500000000)
      constant := (28475175876192317522581956214252674870599063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree022.table
  base := (-1831074080185334028599809854425269930453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-631233593157093639228367988557500000000000)
      constant := (3181344995570787007743191597035748816746059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57249828242206329517/25000000000000000000)
  centralHi := (228999312968825318069/100000000000000000000)
  directionLo := (234388269400548709167/100000000000000000000)
  directionHi := (14649266837534294323/6250000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree023.table
  base := (-749754145207774480057869204663335651517/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 873000000000000000000000000000000000000000
      center := (6984)
      previous := (3492)
      next := (3492)
      square := (106762036560590552386473815490000000000000)
      linear := (-2369308680951923438970548004841687500000000)
      constant := (12490610255724318961988472530207029558256909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree023.table
  base := (-754344340791824888052161772234694824173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 97000000000000000000000000000000000000000
      center := (776)
      previous := (388)
      next := (388)
      square := (11862448506732283598497090610000000000000)
      linear := (-263989005918846060415663963643000000000000)
      constant := (1395539461325683931003155159342234602055219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234388269400548709167/100000000000000000000)
  centralHi := (14649266837534294323/6250000000000000000)
  directionLo := (47931215851457133333/20000000000000000000)
  directionHi := (119828039628642833333/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree024.table
  base := (-932507648097304087806589251731983979/1220703125000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-343400301940642084356797991938125000000000)
      constant := (1895557423725468501600100627701973307833888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree024.table
  base := (-7682360208832856193736533123053945642531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-2754845745748546651399807318630000000000000)
      constant := (15248891760021933436789668752583767272674493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47931215851457133333/20000000000000000000)
  centralHi := (119828039628642833333/50000000000000000000)
  directionLo := (1912582524410631439/781250000000000000)
  directionHi := (244810563124560824193/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree025.table
  base := (-3853566632916296724964041766524188490851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4365000000000000000000000000000000000000000
      center := (34920)
      previous := (17460)
      next := (17460)
      square := (533810182802952761932369077450000000000000)
      linear := (-12878278334966612878836715395336562500000000)
      constant := (74308443255386049703599904025402569482643327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree025.table
  base := (-7747829862729546801284888535017333944933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-2869801432308632698642975000830000000000000)
      constant := (16605213458071724702764750282853318607341499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1912582524410631439/781250000000000000)
  centralHi := (244810563124560824193/100000000000000000000)
  directionLo := (62464683676935987329/25000000000000000000)
  directionHi := (249858734707743949317/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree026.table
  base := (-481733483761301957546720603489631402207/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1091250000000000000000000000000000000000000
      center := (8730)
      previous := (4365)
      next := (4365)
      square := (133452545700738190483092269362500000000000)
      linear := (-3348536450017527680207175770225156250000000)
      constant := (20163878890724338849430955452092184138152828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree026.table
  base := (-774596278461010265283018883252208766211/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 97000000000000000000000000000000000000000
      center := (776)
      previous := (388)
      next := (388)
      square := (11862448506732283598497090610000000000000)
      linear := (-298475711886871874588614268303000000000000)
      constant := (1802376699715104025883943621142535749677533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62464683676935987329/25000000000000000000)
  centralHi := (249858734707743949317/100000000000000000000)
  directionLo := (254806912783277843471/100000000000000000000)
  directionHi := (15925432048954865217/6250000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree027.table
  base := (-477900883568905058846740480038004918163/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-772778514731867142378927264803593750000000)
      constant := (4848826758560671802024406079468292421830881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree027.table
  base := (-7682268957942037485211364750135151750037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-3099712805428804793129310365230000000000000)
      constant := (19504017908863531272540350257046890280246411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254806912783277843471/100000000000000000000)
  centralHi := (15925432048954865217/6250000000000000000)
  directionLo := (259660813937211466397/100000000000000000000)
  directionHi := (129830406968605733199/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree028.table
  base := (-1505627187892087205029504971320963542983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1746000000000000000000000000000000000000000
      center := (13968)
      previous := (6984)
      next := (6984)
      square := (213524073121181104772947630980000000000000)
      linear := (-5770352292110842561925071380811500000000000)
      constant := (37670549289080243085640438882917314451975841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree028.table
  base := (-3780859972981175428386933915370854280689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-1607334245994445420186239023715000000000000)
      constant := (10522741975787604393353991810029027134773167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259660813937211466397/100000000000000000000)
  centralHi := (129830406968605733199/50000000000000000000)
  directionLo := (264425629973581311589/100000000000000000000)
  directionHi := (26442562997358131159/10000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree029.table
  base := (-919673257169978807852664931633341889061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2182500000000000000000000000000000000000000
      center := (17460)
      previous := (8730)
      next := (8730)
      square := (266905091401476380966184538725000000000000)
      linear := (-7470874097690302123402333068796406250000000)
      constant := (50673016302731005143583876577218244876152619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree029.table
  base := (-7388803128904628387600983974613273706151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-3329624178548976887615645729630000000000000)
      constant := (22647729849403414996194257568132512450503353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264425629973581311589/100000000000000000000)
  centralHi := (26442562997358131159/10000000000000000000)
  directionLo := (134553046490329915329/50000000000000000000)
  directionHi := (269106092980659830659/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree030.table
  base := (-1427642924927683416843219241992835323521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 194000000000000000000000000000000000000000
      center := (1552)
      previous := (776)
      next := (776)
      square := (23724897013464567196994181220000000000000)
      linear := (-687005140465960092835406836584750000000000)
      constant := (4834937418620272046466596480571636379868463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree030.table
  base := (-895946216816692767246794739983344373877/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-430572483138632866857351676478750000000000)
      constant := (3038795329156872088893981570209115595733931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134553046490329915329/50000000000000000000)
  centralHi := (269106092980659830659/100000000000000000000)
  directionLo := (273706530378260659093/100000000000000000000)
  directionHi := (136853265189130329547/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree031.table
  base := (-137485592838249625718847151549360848153/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9000000000000000000000000000000000000000
      center := (72)
      previous := (36)
      next := (36)
      square := (1100639552171036622540967170000000000000)
      linear := (-32935016753788865836677611358187500000000)
      constant := (240195782362709136934995084253751906364365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree031.table
  base := (-6901677702012525217988318084258187294471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-3559535551669148982101981094030000000000000)
      constant := (26033027483031040919901618744156955832436313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273706530378260659093/100000000000000000000)
  centralHi := (136853265189130329547/50000000000000000000)
  directionLo := (278230911769515494733/100000000000000000000)
  directionHi := (139115455884757747367/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree032.table
  base := (-6568885210070148895644721298238290854439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-32978701181382195545561258388570000000000000)
      constant := (248942355892595548934646925320777972084074753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree032.table
  base := (-1648607529016221676447485934701135574897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-918622809557308757336287194057500000000000)
      constant := (6953850999878361660465822356573989849234991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278230911769515494733/100000000000000000000)
  centralHi := (139115455884757747367/50000000000000000000)
  directionLo := (282682889040858125093/100000000000000000000)
  directionHi := (141341444520429062547/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree033.table
  base := (-622501591312335084292546557404270966617/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 97000000000000000000000000000000000000000
      center := (776)
      previous := (388)
      next := (388)
      square := (11862448506732283598497090610000000000000)
      linear := (-377893734573213235883835930663312500000000)
      constant := (2949187992204143163472879261549958079519401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree033.table
  base := (-781101220998981501315481559719316568551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-473680865598665134573539557303750000000000)
      constant := (3707150356493246876543729587680976292850553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282682889040858125093/100000000000000000000)
  centralHi := (141341444520429062547/50000000000000000000)
  directionLo := (287065830862672155673/100000000000000000000)
  directionHi := (143532915431336077837/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree034.table
  base := (-730670974280247048404665359288783364963/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1091250000000000000000000000000000000000000
      center := (8730)
      previous := (4365)
      next := (4365)
      square := (133452545700738190483092269362500000000000)
      linear := (-4380271380224523364191151141353281250000000)
      constant := (35305155682934069604647452617060328157543551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree034.table
  base := (-5867510287460475897564802523726426664119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-3904402611349407123831484140630000000000000)
      constant := (31558162758250921719119909022018536613580457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287065830862672155673/100000000000000000000)
  centralHi := (143532915431336077837/50000000000000000000)
  directionLo := (291382852517553764767/100000000000000000000)
  directionHi := (9105714141173555149/3125000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree035.table
  base := (-2716188146459518581596138037202175282839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4365000000000000000000000000000000000000000
      center := (34920)
      previous := (17460)
      next := (17460)
      square := (533810182802952761932369077450000000000000)
      linear := (-18036952986001591298756592250977187500000000)
      constant := (149991604124608583075746063230772464356987803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree035.table
  base := (-136324105358031633707639944756114124359/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24250000000000000000000000000000000000000
      center := (194)
      previous := (97)
      next := (97)
      square := (2965612126683070899624272652500000000000)
      linear := (-100483957447737329276866295570750000000000)
      constant := (837951194051569689624460110209906929937177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291382852517553764767/100000000000000000000)
  centralHi := (9105714141173555149/3125000000000000000)
  directionLo := (295636841807066866089/100000000000000000000)
  directionHi := (29563684180706686609/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree036.table
  base := (-62353018223053165528252105801369133117/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24250000000000000000000000000000000000000
      center := (194)
      previous := (97)
      next := (97)
      square := (2965612126683070899624272652500000000000)
      linear := (-103071224728361606337492110758562500000000)
      constant := (883474686147501630647509658118614466300302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree036.table
  base := (-2503684163443671147299850587459739752647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-2067156992234789609158909752515000000000000)
      constant := (17768322387942599891267768479756405243993241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295636841807066866089/100000000000000000000)
  centralHi := (29563684180706686609/10000000000000000000)
  directionLo := (14991524082464636959/5000000000000000000)
  directionHi := (299830481649292739181/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree037.table
  base := (-4514950710043181476475854361410504152969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-38137375832417173965481135244210625000000000)
      constant := (336642546736567508350187244500350822257270563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree037.table
  base := (-1133176625814946741298678011147187616157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-1062317417757416316390246796807500000000000)
      constant := (9403440340885588382400697384196222801232771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14991524082464636959/5000000000000000000)
  centralHi := (299830481649292739181/100000000000000000000)
  directionLo := (303966269869597637979/100000000000000000000)
  directionHi := (15198313493479881899/5000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree038.table
  base := (-4014299399111302428273163906682856450781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-39169110762624169649465110615338750000000000)
      constant := (355756620079421075571738695481945885849718187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree038.table
  base := (-4030770360533832519542649928125296407661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-4364225357589751312804154869430000000000000)
      constant := (39749223738176011209713316245911846248456883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303966269869597637979/100000000000000000000)
  centralHi := (15198313493479881899/5000000000000000000)
  directionLo := (77011634149826370441/25000000000000000000)
  directionHi := (61609307319861096353/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree039.table
  base := (-1743954684550394189220352598419466729101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-2233380316268398074080504777025937500000000)
      constant := (20855093953989096794257187499937884481183453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree039.table
  base := (-1751588945164810422554508195104366436977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-2239590522074918680023661275815000000000000)
      constant := (20971437477299509529891481717559876455613231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77011634149826370441/25000000000000000000)
  centralHi := (61609307319861096353/20000000000000000000)
  directionLo := (7801836490661086751/2500000000000000000)
  directionHi := (312073459626443470041/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree040.table
  base := (-734311432043883177651703622707572867313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2182500000000000000000000000000000000000000
      center := (17460)
      previous := (8730)
      next := (8730)
      square := (266905091401476380966184538725000000000000)
      linear := (-10308145155759540254358265339398750000000000)
      constant := (98886620243572107400237936374273554511835751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree040.table
  base := (-1475695143243676759706240612682685500219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-2297068365354961703645245116915000000000000)
      constant := (22097286638504438763396210067169779506478757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7801836490661086751/2500000000000000000)
  centralHi := (312073459626443470041/100000000000000000000)
  directionLo := (316049077985694546707/100000000000000000000)
  directionHi := (79012269496423636677/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree041.table
  base := (-472726399314734119103459372453670556423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1746000000000000000000000000000000000000000
      center := (13968)
      previous := (6984)
      next := (6984)
      square := (213524073121181104772947630980000000000000)
      linear := (-8452863110649031340283407345744625000000000)
      constant := (83243966810741449096128943829464001268305221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree041.table
  base := (-475345428203144353486781176408517879791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 194000000000000000000000000000000000000000
      center := (1552)
      previous := (776)
      next := (776)
      square := (23724897013464567196994181220000000000000)
      linear := (-941818483454001890906731583206000000000000)
      constant := (9300838140996148712383708556614373765660273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316049077985694546707/100000000000000000000)
  centralHi := (79012269496423636677/25000000000000000000)
  directionLo := (319975304028291883717/100000000000000000000)
  directionHi := (159987652014145941859/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree042.table
  base := (-1768263790108672526244711395100439022513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-4810672275939128042822334677761250000000000)
      constant := (48601189626383892243917327985474808196066239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree042.table
  base := (-445095041725602012947596075931067859741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-1206012025957523875444206399557500000000000)
      constant := (12217902910588702991571868317199686417605123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319975304028291883717/100000000000000000000)
  centralHi := (159987652014145941859/50000000000000000000)
  directionLo := (323853934174633757869/100000000000000000000)
  directionHi := (32385393417463375787/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree043.table
  base := (-115222118100777599813094251742838984553/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 873000000000000000000000000000000000000000
      center := (6984)
      previous := (3492)
      next := (3492)
      square := (106762036560590552386473815490000000000000)
      linear := (-4432778541365914806938498747097937500000000)
      constant := (45911815582247740541135197855722111429766481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree043.table
  base := (-58171279540075057207070739677166679693/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48500000000000000000000000000000000000000
      center := (388)
      previous := (194)
      next := (194)
      square := (5931224253366141799248545305000000000000)
      linear := (-246950189519509077450999664021500000000000)
      constant := (2564836584757281806452412012805814832069779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323853934174633757869/100000000000000000000)
  centralHi := (32385393417463375787/10000000000000000000)
  directionLo := (6553733170423654221/2000000000000000000)
  directionHi := (327686658521182711051/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree044.table
  base := (-258239932027618007269488458544342323479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4365000000000000000000000000000000000000000
      center := (34920)
      previous := (17460)
      next := (17460)
      square := (533810182802952761932369077450000000000000)
      linear := (-22679760171933071876684481421053750000000000)
      constant := (240670664913613858255498455916341140714102833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree044.table
  base := (-263417672316682421493440990355333992227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-2526979738475133798131580481315000000000000)
      constant := (26889728292978470380873177467995532602753981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6553733170423654221/2000000000000000000)
  centralHi := (327686658521182711051/100000000000000000000)
  directionLo := (82868767361853674389/25000000000000000000)
  directionHi := (331475069447414697557/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree045.table
  base := (138078756427601057529099677022672559429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-5154583919341459937483659801470625000000000)
      constant := (56008828798414825346199770094925618183577113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree045.table
  base := (1285128274364118936269494286309426827/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48500000000000000000000000000000000000000
      center := (388)
      previous := (194)
      next := (194)
      square := (5931224253366141799248545305000000000000)
      linear := (-258445758175517682175316432241500000000000)
      constant := (2815985058680233186772566481596360072011095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82868767361853674389/25000000000000000000)
  centralHi := (331475069447414697557/100000000000000000000)
  directionLo := (41902583668395114011/12500000000000000000)
  directionHi := (335220669347160912089/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree046.table
  base := (810658454435218575928673304969032870219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-47422990204280135121336913584363750000000000)
      constant := (527331848792691724197162787635141266476951187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree046.table
  base := (801826241493294852537705620566052841649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-5283870850070439690749496327030000000000000)
      constant := (58917388567749095231486414083974907125639953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41902583668395114011/12500000000000000000)
  centralHi := (335220669347160912089/100000000000000000000)
  directionLo := (84731219397703693423/25000000000000000000)
  directionHi := (338924877590814773693/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree047.table
  base := (15005399507357693396380632334057405459/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218250000000000000000000000000000000000000
      center := (1746)
      previous := (873)
      next := (873)
      square := (26690509140147638096618453872500000000000)
      linear := (-1211368128362178270133022223887296875000000)
      constant := (13777446767933330053714988872372612636047080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree047.table
  base := (23318578607927953461624328009470175663/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-674853317078815717249083001153750000000000)
      constant := (7696556166165891929208508702586598856314488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84731219397703693423/25000000000000000000)
  centralHi := (338924877590814773693/100000000000000000000)
  directionLo := (2740712294479246143/800000000000000000)
  directionHi := (85647259202476441969/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree048.table
  base := (1103536738411180824867619300164305623131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-2749247781371895916072492462590000000000000)
      constant := (31965386539541741417608294427282812645443707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree048.table
  base := (274944337772040421348300633699557665857/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-689222777898826473154478961428750000000000)
      constant := (8035602593558631794012493036248857093588129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2740712294479246143/800000000000000000)
  centralHi := (85647259202476441969/25000000000000000000)
  directionLo := (173107209291474310931/50000000000000000000)
  directionHi := (346214418582948621863/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree049.table
  base := (2929672057476941745425523929861144240651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-50518194994901122173288839697748125000000000)
      constant := (600168597346580793369038270333259447867400823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree049.table
  base := (365342426520277714522235868829976349699/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-703592238718837229059874921703750000000000)
      constant := (8381805774048809749615697911310257705920803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173107209291474310931/50000000000000000000)
  centralHi := (346214418582948621863/100000000000000000000)
  directionLo := (349802228590841529043/100000000000000000000)
  directionHi := (87450557147710382261/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree050.table
  base := (733561088499698098854840896559624247509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1746000000000000000000000000000000000000000
      center := (13968)
      previous := (6984)
      next := (6984)
      square := (213524073121181104772947630980000000000000)
      linear := (-10309985985021623571454563013775250000000000)
      constant := (125094465342679211200450192170816962124325357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree050.table
  base := (1830707948406149455318002395487887043017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-2871846798155391939861083527915000000000000)
      constant := (34940637258239143104438997015612325043172649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349802228590841529043/100000000000000000000)
  centralHi := (87450557147710382261/25000000000000000000)
  directionLo := (176676805650536328183/50000000000000000000)
  directionHi := (353353611301072656367/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree051.table
  base := (2210497312430065021152124353870183957343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-2921203603073061863403155024444687500000000)
      constant := (36182651535503481613892523483844179816518521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree051.table
  base := (2207553994114400185073224351443261699073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-2929324641435434963482667369015000000000000)
      constant := (36382629766223198396653894226554996384810081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176676805650536328183/50000000000000000000)
  centralHi := (353353611301072656367/100000000000000000000)
  directionLo := (178434827116162872503/50000000000000000000)
  directionHi := (356869654232325745007/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree052.table
  base := (20268776908684143200746228128945365493/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1091250000000000000000000000000000000000000
      center := (8730)
      previous := (4365)
      next := (4365)
      square := (133452545700738190483092269362500000000000)
      linear := (-6701674973190263653155095726391562500000000)
      constant := (84701802795320766273510357589347493121037448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree052.table
  base := (2591692831536415442598423996579571427139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-2986802484715477987104251210115000000000000)
      constant := (37853179764015468457446133299448218428432483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178434827116162872503/50000000000000000000)
  centralHi := (356869654232325745007/100000000000000000000)
  directionLo := (360351391844529890611/100000000000000000000)
  directionHi := (90087847961132472653/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree053.table
  base := (5970851335412940660136447641428266279363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-54645134715729104909224741182260625000000000)
      constant := (704452069629625429604950721417649850094696399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree053.table
  base := (1491465142703032186702946971293052065909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-1522140163997760505362917525607500000000000)
      constant := (19676134208307569296965203308812926050393173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360351391844529890611/100000000000000000000)
  centralHi := (90087847961132472653/25000000000000000000)
  directionLo := (90949952273448209529/25000000000000000000)
  directionHi := (363799809093792838117/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree054.table
  base := (845846855401204727848756179515159274089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-773289856193556952683454396574843750000000)
      constant := (10163893905065516685987234327458695547242883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree054.table
  base := (422636374707044130649222123758890734227/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-775439542818891008586854723078750000000000)
      constant := (10219969678572427598668358508186724802440038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90949952273448209529/25000000000000000000)
  centralHi := (363799809093792838117/100000000000000000000)
  directionLo := (5737747573231894317/1562500000000000000)
  directionHi := (367215844686841236289/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree055.table
  base := (7576258415675090043155468026820521008433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-56708604576143096277192691924516875000000000)
      constant := (759659018484038247489509878647940218160674509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree055.table
  base := (757203320778049673727882535772035130751/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 97000000000000000000000000000000000000000
      center := (776)
      previous := (388)
      next := (388)
      square := (11862448506732283598497090610000000000000)
      linear := (-631847202911121411593800546683000000000000)
      constant := (8487199059138534330002183496034887407682847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5737747573231894317/1562500000000000000)
  centralHi := (367215844686841236289/100000000000000000000)
  directionLo := (185300197032720728743/50000000000000000000)
  directionHi := (370600394065441457487/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree056.table
  base := (1679802776855156838687434896008347597593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1746000000000000000000000000000000000000000
      center := (13968)
      previous := (6984)
      next := (6984)
      square := (213524073121181104772947630980000000000000)
      linear := (-11548067901270018392235333459129000000000000)
      constant := (157605558003291762187934449174292099952698689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree056.table
  base := (8395128173128645790675434057289213569233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-6433427715671300163181173149030000000000000)
      constant := (88041208576244619794895127627637053716215601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185300197032720728743/50000000000000000000)
  centralHi := (370600394065441457487/100000000000000000000)
  directionLo := (373954312147688285879/100000000000000000000)
  directionHi := (9348857803692207147/2500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree057.table
  base := (577173808069251659551104459114000284533/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-1632557623237696879032240074077031250000000)
      constant := (22691845791741749086758174943715862237351929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree057.table
  base := (9231208575521187712169038703918325068871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-6548383402231386210424340831230000000000000)
      constant := (91267386326521161616741136953990077531680487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373954312147688285879/100000000000000000000)
  centralHi := (9348857803692207147/2500000000000000000)
  directionLo := (377278415849940821297/100000000000000000000)
  directionHi := (188639207924970410649/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree058.table
  base := (2520831096906664168839190215426939737761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2182500000000000000000000000000000000000000
      center := (17460)
      previous := (8730)
      next := (8730)
      square := (266905091401476380966184538725000000000000)
      linear := (-14950952341691020832286154509475312500000000)
      constant := (211573697161467197742767560577061160773877853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree058.table
  base := (5040020566081411135955047419788392907207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-3331669544395736128833754256715000000000000)
      constant := (47275250606891912321632228563489474111999079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377278415849940821297/100000000000000000000)
  centralHi := (188639207924970410649/50000000000000000000)
  directionLo := (190286743205242143559/50000000000000000000)
  directionHi := (380573486410484287119/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree059.table
  base := (342013494482963051615641081237122549071/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2182500000000000000000000000000000000000000
      center := (17460)
      previous := (8730)
      next := (8730)
      square := (266905091401476380966184538725000000000000)
      linear := (-15208886074242769753282148352257343750000000)
      constant := (219048156247249821600283524839286393228414989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree059.table
  base := (273535379185045749407372057871009849299/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24250000000000000000000000000000000000000
      center := (194)
      previous := (97)
      next := (97)
      square := (2965612126683070899624272652500000000000)
      linear := (-169457369383788957622766904890750000000000)
      constant := (2447263320062359802089638182302737955382003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190286743205242143559/50000000000000000000)
  centralHi := (380573486410484287119/100000000000000000000)
  directionLo := (383840271533643612803/100000000000000000000)
  directionHi := (95960067883410903201/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree060.table
  base := (590895566507050592726983477143198934099/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48500000000000000000000000000000000000000
      center := (388)
      previous := (194)
      next := (194)
      square := (5931224253366141799248545305000000000000)
      linear := (-343707106817655970539514271000875000000000)
      constant := (5036665499987568311026916013927675452857603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree060.table
  base := (11815140421920041146665453176672546278041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-6893250461911644352153843877830000000000000)
      constant := (101287462637499001478874526497937236988969977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383840271533643612803/100000000000000000000)
  centralHi := (95960067883410903201/25000000000000000000)
  directionLo := (387079487371019765369/100000000000000000000)
  directionHi := (38707948737101976537/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree061.table
  base := (2540717909431707839358143138182208692433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1746000000000000000000000000000000000000000
      center := (13968)
      previous := (6984)
      next := (6984)
      square := (213524073121181104772947630980000000000000)
      linear := (-12579802831477014076219308830257125000000000)
      constant := (187503226465683602109235737505441428540056509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree061.table
  base := (2540209014845666840298221768362672777287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 194000000000000000000000000000000000000000
      center := (1552)
      previous := (776)
      next := (776)
      square := (23724897013464567196994181220000000000000)
      linear := (-1401641229694346079879402312006000000000000)
      constant := (20948254810422641607144595396377179259396839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387079487371019765369/100000000000000000000)
  centralHi := (38707948737101976537/10000000000000000000)
  directionLo := (195145910177360391987/50000000000000000000)
  directionHi := (15611672814188831359/4000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree062.table
  base := (6800654933818282140297191000892756336469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4365000000000000000000000000000000000000000
      center := (34920)
      previous := (17460)
      next := (17460)
      square := (533810182802952761932369077450000000000000)
      linear := (-31965374543796033032540259761206875000000000)
      constant := (484470757631584095391402185399102745422362437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree062.table
  base := (13598973953893808736791112693073075356551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-7123161835031816446640179242230000000000000)
      constant := (108251951994805020414944747292088088309585447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195145910177360391987/50000000000000000000)
  centralHi := (15611672814188831359/4000000000000000000)
  directionLo := (196738964447940403213/50000000000000000000)
  directionHi := (393477928895880806427/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree063.table
  base := (3627732704823543051062470804145800343173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-902256722469431413181451317965859375000000)
      constant := (13901052990232105527576904816513239895745453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree063.table
  base := (453399591497453557366996668613494557931/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-904764690198987811735418365553750000000000)
      constant := (13977435359084204672201018126133285888477228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196738964447940403213/50000000000000000000)
  centralHi := (393477928895880806427/100000000000000000000)
  directionLo := (49579805620046495923/12500000000000000000)
  directionHi := (79327688992074393477/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree064.table
  base := (15432324601839340672718377006432087214151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-65994218948006057433048470264670000000000000)
      constant := (1033318920859393296690808106146345212137953823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree064.table
  base := (15430357443490143056967954352694338415953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-7353073208151988541126514606630000000000000)
      constant := (115443854410096265198899164962931350826347441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49579805620046495923/12500000000000000000)
  centralHi := (79327688992074393477/20000000000000000000)
  directionLo := (399773975532390318907/100000000000000000000)
  directionHi := (99943493883097579727/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree065.table
  base := (8182687882856144334739724601979026374437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4365000000000000000000000000000000000000000
      center := (34920)
      previous := (17460)
      next := (17460)
      square := (533810182802952761932369077450000000000000)
      linear := (-33512976939106526558516222817899062500000000)
      constant := (533135365581873799035597463651131852622539751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree065.table
  base := (16363571211951157102559061274896966186313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-7468028894712074588369682288830000000000000)
      constant := (119125055521073122566921096427615005720072361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399773975532390318907/100000000000000000000)
  centralHi := (99943493883097579727/25000000000000000000)
  directionLo := (402885103975516081873/100000000000000000000)
  directionHi := (201442551987758040937/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree066.table
  base := (173099800185138807543874831155530751271/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48500000000000000000000000000000000000000
      center := (388)
      previous := (194)
      next := (194)
      square := (5931224253366141799248545305000000000000)
      linear := (-378098271157889160005646783371812500000000)
      constant := (6109617528680611427152502704906605265928935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree066.table
  base := (4327081255075317826170770353474230760159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-1895746145318040158903212492757500000000000)
      constant := (30715769048485795467223507131632000383735423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402885103975516081873/100000000000000000000)
  centralHi := (201442551987758040937/50000000000000000000)
  directionLo := (405972391299891962287/100000000000000000000)
  directionHi := (25373274456243247643/6250000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree067.table
  base := (570813848336868019402216730056015813427/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2182500000000000000000000000000000000000000
      center := (17460)
      previous := (8730)
      next := (8730)
      square := (266905091401476380966184538725000000000000)
      linear := (-17272355934656761121250099094513593750000000)
      constant := (283425027651831576012984456879720805505427293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree067.table
  base := (2283065707234302173284152267304345399639/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-962242533479030835357002206653750000000000)
      constant := (15832238423408979310242810248304771503764983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405972391299891962287/100000000000000000000)
  centralHi := (25373274456243247643/6250000000000000000)
  directionLo := (409036377343315011257/100000000000000000000)
  directionHi := (204518188671657505629/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree068.table
  base := (19233480041953463713775550565648044685777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-70121158668834040168984371749182500000000000)
      constant := (1168177523198426504104007284265200821135683321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree068.table
  base := (3846417789405789472490919244736484057357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 194000000000000000000000000000000000000000
      center := (1552)
      previous := (776)
      next := (776)
      square := (23724897013464567196994181220000000000000)
      linear := (-1562579190878466546019837067086000000000000)
      constant := (26101908187165568110306718782107438953563629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409036377343315011257/100000000000000000000)
  centralHi := (204518188671657505629/50000000000000000000)
  directionLo := (206038790936641938389/50000000000000000000)
  directionHi := (412077581873283876779/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree069.table
  base := (10106106910244261824437558036630798560371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-3952938533280057547387130395572812500000000)
      constant := (66842406989804146321901631859740201620512237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree069.table
  base := (20210938867771445580827170711068199729239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-7927851640952418777342353017630000000000000)
      constant := (134417969465671838759384559937843615373736183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206038790936641938389/50000000000000000000)
  centralHi := (412077581873283876779/100000000000000000000)
  directionLo := (415096505616372501323/100000000000000000000)
  directionHi := (103774126404093125331/25000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree070.table
  base := (5300543757245899205811415983767180532641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2182500000000000000000000000000000000000000
      center := (17460)
      previous := (8730)
      next := (8730)
      square := (266905091401476380966184538725000000000000)
      linear := (-18046157132312007884238080622859687500000000)
      constant := (309664364457162826547312867782320472237808093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree070.table
  base := (21201006767211299577945070567240561963893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-8042807327512504824585520699830000000000000)
      constant := (138383186317473439696541130578122334510497621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415096505616372501323/100000000000000000000)
  centralHi := (103774126404093125331/25000000000000000000)
  directionLo := (209046815610351595693/50000000000000000000)
  directionHi := (418093631220703191387/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree071.table
  base := (888132037045303351067419006359813769569/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1746000000000000000000000000000000000000000
      center := (13968)
      previous := (6984)
      next := (6984)
      square := (213524073121181104772947630980000000000000)
      linear := (-14643272691891005444187259572513375000000000)
      constant := (254931972892359259292063495309398986518231185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree071.table
  base := (2775278830703163578219395166229482918889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-1019720376759073858978586047753750000000000)
      constant := (17800648184657436611547768973565509843132233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209046815610351595693/50000000000000000000)
  centralHi := (418093631220703191387/100000000000000000000)
  directionLo := (105267356039189432209/25000000000000000000)
  directionHi := (421069424156757728837/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree072.table
  base := (23215534834066744239351584431206393473309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-8249788709962446989435585914855000000000000)
      constant := (145685610692903354927983831223276082666910973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree072.table
  base := (5803638627927063319020872403273949588491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-2068179675158169229767964016057500000000000)
      constant := (36620990378468348015108687522657573110083627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105267356039189432209/25000000000000000000)
  centralHi := (421069424156757728837/100000000000000000000)
  directionLo := (10600608339032179691/2500000000000000000)
  directionHi := (424024333561287187641/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree073.table
  base := (2423882555238273486808467867497009890343/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 873000000000000000000000000000000000000000
      center := (6984)
      previous := (3492)
      next := (3492)
      square := (106762036560590552386473815490000000000000)
      linear := (-7527983331986901858890424860482312500000000)
      constant := (134818930845370088112528440420076448716300689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree073.table
  base := (24237927800304793730614901174408275958309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-8387674387192762966315023746430000000000000)
      constant := (150619509522495069240262355522907602767955973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10600608339032179691/2500000000000000000)
  centralHi := (424024333561287187641/100000000000000000000)
  directionLo := (426958793028652743859/100000000000000000000)
  directionHi := (21347939651432637193/5000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree074.table
  base := (25273126828798680591662733732711144751827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-76311568250076014272888223975951250000000000)
      constant := (1385716260736266279843430419031270911399594971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree074.table
  base := (1579519052910486910952968028031802487079/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-1062828759219106126694773928578750000000000)
      constant := (19351478134204293988587135381440669682493326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426958793028652743859/100000000000000000000)
  centralHi := (21347939651432637193/5000000000000000000)
  directionLo := (107468305338386315351/25000000000000000000)
  directionHi := (85974644270709052281/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree075.table
  base := (5263679376193160348769614434523806835881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 194000000000000000000000000000000000000000
      center := (1552)
      previous := (776)
      next := (776)
      square := (23724897013464567196994181220000000000000)
      linear := (-1718740070672955776819382207712875000000000)
      constant := (31638918146840797907948156291178521177142957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree075.table
  base := (13158822205537452237715931432001642439647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-4308792880156467530400679555415000000000000)
      constant := (79530452083533636575143820992529159316645759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107468305338386315351/25000000000000000000)
  centralHi := (85974644270709052281/20000000000000000000)
  directionLo := (27048001451792861083/6250000000000000000)
  directionHi := (432768023228685777329/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree076.table
  base := (27374597964491971839669826405911315659207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-78375038110490005640856174718207500000000000)
      constant := (1462294443117555432746614679011045031695487711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree076.table
  base := (27373909250965233284254880091427020098599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-8732541446873021108044526793030000000000000)
      constant := (163366743190236325456783457323548420949564103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27048001451792861083/6250000000000000000)
  centralHi := (432768023228685777329/100000000000000000000)
  directionLo := (435643589900797809697/100000000000000000000)
  directionHi := (217821794950398904849/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree077.table
  base := (7110423995677831542771599367093923744401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1091250000000000000000000000000000000000000
      center := (8730)
      previous := (4365)
      next := (4365)
      square := (133452545700738190483092269362500000000000)
      linear := (-9925846630087125165605018761166953125000000)
      constant := (187668201312379445077519130107443539340407599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree077.table
  base := (28441065732636295858255909539375511281519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-8847497133433107155287694475230000000000000)
      constant := (167729338880682068157268847899629424594307343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435643589900797809697/100000000000000000000)
  centralHi := (217821794950398904849/50000000000000000000)
  directionLo := (219250149893930913023/50000000000000000000)
  directionHi := (438500299787861826047/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree078.table
  base := (29519660134165618255143580746989081949369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-8937611996767110778758236162273750000000000)
      constant := (171211643540289248922073677557930460480338793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree078.table
  base := (1180763339278953917300074576601410834669/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 194000000000000000000000000000000000000000
      center := (1552)
      previous := (776)
      next := (776)
      square := (23724897013464567196994181220000000000000)
      linear := (-1792490563998638640506172431486000000000000)
      constant := (34429737658423083911609060858879684254814465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219250149893930913023/50000000000000000000)
  centralHi := (438500299787861826047/100000000000000000000)
  directionLo := (220669259530204435903/50000000000000000000)
  directionHi := (441338519060408871807/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree079.table
  base := (15304231297076445587334417012553964077289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4365000000000000000000000000000000000000000
      center := (34920)
      previous := (17460)
      next := (17460)
      square := (533810182802952761932369077450000000000000)
      linear := (-40735121450555496346404050415795937500000000)
      constant := (790485981458646831696726610570696351362129547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree079.table
  base := (3825991883559663834904975810704798360987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-1134676063319159906221753729953750000000000)
      constant := (22078098595472227939102598937409615441015739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220669259530204435903/50000000000000000000)
  centralHi := (441338519060408871807/100000000000000000000)
  directionLo := (444158602189381305551/100000000000000000000)
  directionHi := (27759912636836331597/6250000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree080.table
  base := (6341615645410244893121409710456504137453/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1746000000000000000000000000000000000000000
      center := (13968)
      previous := (6984)
      next := (6984)
      square := (213524073121181104772947630980000000000000)
      linear := (-16500395566263597675358415240544000000000000)
      constant := (324309420343941778667880660056092278111996469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree080.table
  base := (15853797859998032786671606811152764327849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-4596182096556682648508598760915000000000000)
      constant := (90578818946385335012329018433881818139801353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444158602189381305551/100000000000000000000)
  centralHi := (27759912636836331597/6250000000000000000)
  directionLo := (223480446231440608059/50000000000000000000)
  directionHi := (446960892462881216119/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree081.table
  base := (32818484326443475392060258034301446509977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-9281523640169442673419561285983125000000000)
      constant := (184736687605238529392008267873748182694280269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree081.table
  base := (820451076627754628264869618390802747139/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24250000000000000000000000000000000000000
      center := (194)
      previous := (97)
      next := (97)
      square := (2965612126683070899624272652500000000000)
      linear := (-232682996991836283606509130100750000000000)
      constant := (4643680837726655653189699054854657866472483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223480446231440608059/50000000000000000000)
  centralHi := (446960892462881216119/100000000000000000000)
  directionLo := (44974572247393910877/10000000000000000000)
  directionHi := (449745722473939108771/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree082.table
  base := (2121228773772271582693406662148009199289/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1091250000000000000000000000000000000000000
      center := (8730)
      previous := (4365)
      next := (4365)
      square := (133452545700738190483092269362500000000000)
      linear := (-10570680961466497468095003368122031250000000)
      constant := (213027650649081823406832651176345758534614844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree082.table
  base := (16969628450238319004556863343384025000043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-4711137783116768695751766443115000000000000)
      constant := (95196786826470108890724065272038250425004171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44974572247393910877/10000000000000000000)
  centralHi := (449745722473939108771/100000000000000000000)
  directionLo := (452513414581264815319/100000000000000000000)
  directionHi := (11312835364531620383/2500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree083.table
  base := (4383948482398342343328071682287184324063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2182500000000000000000000000000000000000000
      center := (17460)
      previous := (8730)
      next := (8730)
      square := (266905091401476380966184538725000000000000)
      linear := (-21399295655484743857186000579026093750000000)
      constant := (436580033944972214784278324546423757081767123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree083.table
  base := (8767804745180404536432186048661142720147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-2384307813198405859686675142107500000000000)
      constant := (48774164138647846449527731568792630843854259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452513414581264815319/100000000000000000000)
  centralHi := (11312835364531620383/2500000000000000000)
  directionLo := (9105285626895750253/2000000000000000000)
  directionHi := (455264281344787512651/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree084.table
  base := (18107125012061464176183334773641944715517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-4812717641785887284040443204846250000000000)
      constant := (99384831421992607901864051629040182699905149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree084.table
  base := (9053478207173525158808148149132705616201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-2413046734838427371497467062657500000000000)
      constant := (49964120153934020190442811663795872444771497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9105285626895750253/2000000000000000000)
  centralHi := (455264281344787512651/100000000000000000000)
  directionLo := (457998625937650636137/100000000000000000000)
  directionHi := (228999312968825318069/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree085.table
  base := (4670953969259989915979906061130849650007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2182500000000000000000000000000000000000000
      center := (17460)
      previous := (8730)
      next := (8730)
      square := (266905091401476380966184538725000000000000)
      linear := (-21915163120588241699177988264590156250000000)
      constant := (458010420359970409018170928209712472522115347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree085.table
  base := (18683661782053729970768645816038159302887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-4883571312956897766616517966415000000000000)
      constant := (102336522196493249997714278799430701452380039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457998625937650636137/100000000000000000000)
  centralHi := (228999312968825318069/50000000000000000000)
  directionLo := (460716742536198939117/100000000000000000000)
  directionHi := (230358371268099469559/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree086.table
  base := (3853171938935980995757868957372096495233/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 873000000000000000000000000000000000000000
      center := (6984)
      previous := (3492)
      next := (3492)
      square := (106762036560590552386473815490000000000000)
      linear := (-8869238741255996248069592842948875000000000)
      constant := (187566427138701667245690590785436248443463409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree086.table
  base := (4816429718598400061256342805842056866393/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-1235262289059235197559525451878750000000000)
      constant := (26193293322854964678543428189664179516040121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460716742536198939117/100000000000000000000)
  centralHi := (230358371268099469559/50000000000000000000)
  directionLo := (4634189166893777241/1000000000000000000)
  directionHi := (463418916689377724101/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree087.table
  base := (7941300118084170507607879097810849505529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 194000000000000000000000000000000000000000
      center := (1552)
      previous := (776)
      next := (776)
      square := (23724897013464567196994181220000000000000)
      linear := (-1993869385394821292548442306680375000000000)
      constant := (42662104992552269014244982398125887753598813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree087.table
  base := (39706243246915534102804128654375741573479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-9997053999033967627719371297230000000000000)
      constant := (214476386008121407607264875221084446932627463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4634189166893777241/1000000000000000000)
  centralHi := (463418916689377724101/100000000000000000000)
  directionLo := (46610542566885724093/10000000000000000000)
  directionHi := (466105425668857240931/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree088.table
  base := (40891964210295116039829796030967930310377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-90755857272973953848663879171745000000000000)
      constant := (1964433031542084931836379772234596565660959121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree088.table
  base := (40891729098819488788974199124750204455851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-10112009685594053674962538979430000000000000)
      constant := (219463161605743292249071051350540769832217547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46610542566885724093/10000000000000000000)
  centralHi := (466105425668857240931/100000000000000000000)
  directionLo := (93755307760219483667/20000000000000000000)
  directionHi := (14649266837534294323/3125000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree089.table
  base := (42088100179335754643651301686464223888063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-91787592203180949532647854542873125000000000)
      constant := (2009579183227913454642724932166310264524591499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree089.table
  base := (42087885406990070767085293827622109691191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-10226965372154139722205706661630000000000000)
      constant := (224506672415646998956962814882749344640045527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93755307760219483667/20000000000000000000)
  centralHi := (14649266837534294323/3125000000000000000)
  directionLo := (471432517782478581763/100000000000000000000)
  directionHi := (117858129445619645441/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree090.table
  base := (43294899401102352976410145588706996321993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-10313258570376438357403536657111250000000000)
      constant := (228359241309016132382149869915117566924483321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree090.table
  base := (43294703233147190794464032216639588617223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-10341921058714225769448874343830000000000000)
      constant := (229606917570819359074400847904714040095870631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471432517782478581763/100000000000000000000)
  centralHi := (117858129445619645441/25000000000000000000)
  directionLo := (474073616978541820061/100000000000000000000)
  directionHi := (237036808489270910031/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree091.table
  base := (11128088414576991835161491028042206652733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1091250000000000000000000000000000000000000
      center := (8730)
      previous := (4365)
      next := (4365)
      square := (133452545700738190483092269362500000000000)
      linear := (-11731382757949367612576975660641171875000000)
      constant := (262674373753511080047296070749844330064269517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree091.table
  base := (8902434901055985903173201811807259877039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 194000000000000000000000000000000000000000
      center := (1552)
      previous := (776)
      next := (776)
      square := (23724897013464567196994181220000000000000)
      linear := (-2091375349054862363338408405206000000000000)
      constant := (46952779257655062684785288621771304208072783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474073616978541820061/100000000000000000000)
  centralHi := (237036808489270910031/50000000000000000000)
  directionLo := (238350041854153743863/50000000000000000000)
  directionHi := (476700083708307487727/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree092.table
  base := (4574045552785550287902178739407856575889/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 873000000000000000000000000000000000000000
      center := (6984)
      previous := (3492)
      next := (3492)
      square := (106762036560590552386473815490000000000000)
      linear := (-9488279699380193658459978065625750000000000)
      constant := (214806463148838003764932896776420066603251097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree092.table
  base := (5717536491711931131168121722735236005257/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121250000000000000000000000000000000000000
      center := (970)
      previous := (485)
      next := (485)
      square := (14828060633415354498121363262500000000000)
      linear := (-1321479053979299732991901213528750000000000)
      constant := (29997200982614332091373851773700317892509929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238350041854153743863/50000000000000000000)
  centralHi := (476700083708307487727/100000000000000000000)
  directionLo := (479312158514571333331/100000000000000000000)
  directionHi := (119828039628642833333/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree093.table
  base := (46979198304085034822054208261512851700869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-10657170213778770252064861780820625000000000)
      constant := (243915787811997585436496780007826009310296793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree093.table
  base := (11744762233800884521944686788839051982637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-2671697029598620977794594347607500000000000)
      constant := (61312012912541984624700777440414888042315789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479312158514571333331/100000000000000000000)
  centralHi := (119828039628642833333/25000000000000000000)
  directionLo := (96382015084202871743/20000000000000000000)
  directionHi := (120477518855253589679/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree094.table
  base := (48228575929438569185117870476207906500837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-96946266854215927952567731398513750000000000)
      constant := (2242927361198635205467216786921450615656480701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree094.table
  base := (4822843956464837956174687467690082945563/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 97000000000000000000000000000000000000000
      center := (776)
      previous := (388)
      next := (388)
      square := (11862448506732283598497090610000000000000)
      linear := (-1080174380495456995842154507263000000000000)
      constant := (25057522707935504447162954573827938045719611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96382015084202871743/20000000000000000000)
  centralHi := (120477518855253589679/25000000000000000000)
  directionLo := (242247031088452113139/50000000000000000000)
  directionHi := (484494062176904226279/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree095.table
  base := (24744291465912711042055786679853945488227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4365000000000000000000000000000000000000000
      center := (34920)
      previous := (17460)
      next := (17460)
      square := (533810182802952761932369077450000000000000)
      linear := (-48989000892211461818275853384820937500000000)
      constant := (1145560219691607840117372960062479157008878421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree095.table
  base := (49488458453075533134528847179833381969491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 970000000000000000000000000000000000000000
      center := (7760)
      previous := (3880)
      next := (3880)
      square := (118624485067322835984970906100000000000000)
      linear := (-10916699491514656005664712754830000000000000)
      constant := (255959133627687393936808232730293838051040627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242247031088452113139/50000000000000000000)
  centralHi := (484494062176904226279/100000000000000000000)
  directionLo := (487064340490112383277/100000000000000000000)
  directionHi := (243532170245056191639/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree096.table
  base := (25379607184020334997445306486105274159359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 485000000000000000000000000000000000000000
      center := (3880)
      previous := (1940)
      next := (1940)
      square := (59312242533661417992485453050000000000000)
      linear := (-5500540928590551073363093452265000000000000)
      constant := (129990073363683433055248894063417211593457823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree096.table
  base := (1268977518797278099498856054888178274033/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 250000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (30573320893639906181693532500000000000)
      linear := (-2843210097441943828069041349750000000000)
      constant := (67371074954858603359845525710888178274033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487064340490112383277/100000000000000000000)
  centralHi := (243532170245056191639/50000000000000000000)
  directionLo := (1912582524410631439/390625000000000000)
  directionHi := (97924225249824329677/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree097.table
  base := (10408093154530340388977613172757274741729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (144)
      previous := (72)
      next := (72)
      square := (2201279104342073245081934340000000000000)
      linear := (-206271075556364773205195170127625000000000)
      constant := (4925835053174372949211068828452199261738061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree097.table
  base := (10408072416486508386729057537978674737623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (16)
      previous := (8)
      next := (8)
      square := (244586567149119249453548260000000000000)
      linear := (-22982702813680057938455769318000000000000)
      constant := (550303377827044809451262109143978674737623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell045.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1912582524410631439/390625000000000000)
  centralHi := (97924225249824329677/20000000000000000000)
  directionLo := (246082314867326716881/50000000000000000000)
  directionHi := (492164629734653433763/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree098.table
  base := (53332333111824435743456636329500035571793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8730000000000000000000000000000000000000000
      center := (69840)
      previous := (34920)
      next := (34920)
      square := (1067620365605905523864738154900000000000000)
      linear := (-101073206575043910688503632883026250000000000)
      constant := (2438746476591485782600975696947970269335425289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree098.table
  base := (13333059622606557295423455867980564903587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242500000000000000000000000000000000000000
      center := (1940)
      previous := (970)
      next := (970)
      square := (29656121266830708996242726525000000000000)
      linear := (-2815391637798728536848553950357500000000000)
      constant := (68112808876979728367960897680379114795647939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell045.Kernel098
