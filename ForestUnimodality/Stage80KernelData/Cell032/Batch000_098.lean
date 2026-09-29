import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell032.Parameters
import ForestUnimodality.BinomialMassData.Q841_1786.Batch000_049
import ForestUnimodality.BinomialMassData.Q841_1786.Batch050_099
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch000_049
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree000.table
  base := (246761928984978939577388249/5000000000000000000000000)
  polynomial :=
    { denominator := 17860000000000000000000000000000000000000000
      center := (101115)
      previous := (89987)
      next := (0)
      square := (4228509781648704723977516553800000000000000)
      linear := (16883058484111368018343313214600000000000000)
      constant := (881433610334344772170430825428000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree000.table
  base := (246761928984978939577388249/5000000000000000000000000)
  polynomial :=
    { denominator := 35720000000000000000000000000000000000000000
      center := (201695)
      previous := (180509)
      next := (0)
      square := (8457019563297409447955033107600000000000000)
      linear := (33766116968222736036686626429200000000000000)
      constant := (1762867220668689544340861650856000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree001.table
  base := (59024024625944208318655437366506674831243/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (606336552628678471974499330468000000000000000)
      constant := (24443391714651407436415144031890166493420999530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree001.table
  base := (294533834432409950816155140341771895992721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (1211560339525344126916372998685000000000000000)
      constant := (48786658245702802320036527435039707986841972364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49915157706522119783/100000000000000000000)
  directionHi := (6239394713315264973/12500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree002.table
  base := (18370642310320748027894152055234924196563/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (419169356504122647086862939849800000000000000)
      constant := (14849655407143195282776976378089300069078913460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree002.table
  base := (183051435039501146208673045567592250452693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (836113181544219660108474555197600000000000000)
      constant := (29587004940563964549857268018362157374999911612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49915157706522119783/100000000000000000000)
  centralHi := (6239394713315264973/12500000000000000000)
  directionLo := (70590692996555495851/100000000000000000000)
  directionHi := (17647673249138873963/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree003.table
  base := (29867401424102079447195242519832718613181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (232002160379566822199226549231600000000000000)
      constant := (9304175141720074642455242725670242263310558008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree003.table
  base := (118907372582450904334278770364668176157803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (460666023563095193300576111710200000000000000)
      constant := (18512018842252979570885850831074427086076598852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70590692996555495851/100000000000000000000)
  centralHi := (17647673249138873963/25000000000000000000)
  directionLo := (86455589215509506557/100000000000000000000)
  directionHi := (43227794607754753279/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree004.table
  base := (81053928397634051861522468390489951102337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (44834964255010997311590158613400000000000000)
      constant := (6014307180465805316634159282589307475432372454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree004.table
  base := (80610265987029477297173347890320734156227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (85218865581970726492677668222800000000000000)
      constant := (11953640930503860387383962123760206133084013668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86455589215509506557/100000000000000000000)
  centralHi := (43227794607754753279/50000000000000000000)
  directionLo := (99830315413044239567/100000000000000000000)
  directionHi := (6239394713315264973/6250000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree005.table
  base := (28486345023532766057374376512843121361423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-142332231869544827576046232004800000000000000)
      constant := (4015834854622848183912856203417404586641138932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree005.table
  base := (28314902200558332219678272396495440555121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-290228292399153740315220775264600000000000000)
      constant := (7976116498219259232083890720426356084311867928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99830315413044239567/100000000000000000000)
  centralHi := (6239394713315264973/6250000000000000000)
  directionLo := (111613685739405957607/100000000000000000000)
  directionHi := (13951710717425744701/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree006.table
  base := (10255229946479400095508081571668574857817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-329499427994100652463682622623000000000000000)
      constant := (2787900500363059497485076476368414042859498456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree006.table
  base := (10188226472389428190497045987629497628751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-665675450380278207123119218752000000000000000)
      constant := (5536368497797655552528352325096062319620931536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111613685739405957607/100000000000000000000)
  centralHi := (13951710717425744701/12500000000000000000)
  directionLo := (12226666681153063719/10000000000000000000)
  directionHi := (122266666811530637191/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree007.table
  base := (29822861308318790255368929925743606718979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-516666624118656477351319013241200000000000000)
      constant := (2047136381858976624130126655613019835204535218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree007.table
  base := (29607431702488584400607310021056146281159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-1041122608361402673931017662239400000000000000)
      constant := (4068268787356875215880183911158865062266097556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12226666681153063719/10000000000000000000)
  centralHi := (122266666811530637191/100000000000000000000)
  directionLo := (132063093944026701179/100000000000000000000)
  directionHi := (6603154697201335059/5000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree008.table
  base := (4304408907823367289475397309248428328679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-703833820243212302238955403859400000000000000)
      constant := (1637706688062168111094622371321457853829863090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree008.table
  base := (21342973794280436162049219091292220475897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-1416569766342527140738916105726800000000000000)
      constant := (3261163462564565511498122326832103142375491948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132063093944026701179/100000000000000000000)
  centralHi := (6603154697201335059/5000000000000000000)
  directionLo := (141181385993110991703/100000000000000000000)
  directionHi := (17647673249138873963/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree009.table
  base := (3770180656633197944220050248510457370251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-891001016367768127126591794477600000000000000)
      constant := (1472500872740605574096263055665909250294437768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree009.table
  base := (3731785780290978344910243615742597665473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-1792016924323651607546814549214200000000000000)
      constant := (2941730921196552100522448267465796065881076528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141181385993110991703/100000000000000000000)
  centralHi := (17647673249138873963/12500000000000000000)
  directionLo := (149745473119566359351/100000000000000000000)
  directionHi := (18718184139945794919/12500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree010.table
  base := (4952401810527172734239316591399639731767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-1078168212492323952014228185095800000000000000)
      constant := (1501649669468326622026426937918537116727971028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree010.table
  base := (1221222291304718734259886612248514639157/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-2167464082304776074354712992701600000000000000)
      constant := (3010892514715935611706975753114337053441870304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149745473119566359351/100000000000000000000)
  centralHi := (18718184139945794919/12500000000000000000)
  directionLo := (157845588119116416599/100000000000000000000)
  directionHi := (789227940595582083/500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree011.table
  base := (176334264897290080890913157871389078983/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-1265335408616879776901864575714000000000000000)
      constant := (1695639822664667356923569262585934546175711552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree011.table
  base := (1380478036186157929028987709976887349151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-2542911240285900541162611436189000000000000000)
      constant := (3410062220730860753353896750628714022899465936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157845588119116416599/100000000000000000000)
  centralHi := (789227940595582083/500000000000000000)
  directionLo := (41387462365987661669/25000000000000000000)
  directionHi := (165549849463950646677/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree012.table
  base := (2077129395721836022073670765767894587913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-1452502604741435601789500966332200000000000000)
      constant := (2036233103079727031628897448526088607498593046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree012.table
  base := (1967920560468447980077029915625484294609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-2918358398267025007970509879676400000000000000)
      constant := (4103040219018240358817270417458868805316137356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41387462365987661669/25000000000000000000)
  centralHi := (165549849463950646677/100000000000000000000)
  directionLo := (86455589215509506557/50000000000000000000)
  directionHi := (34582235686203802623/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree013.table
  base := (-186657520369888180921922242271606500667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-1639669800865991426677137356950400000000000000)
      constant := (2511560953018268033451836971156234035605053430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree013.table
  base := (-258149617354076155245240592733314394471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-3293805556248149474778408323163800000000000000)
      constant := (5066255252315244834271909036193715984794522544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86455589215509506557/50000000000000000000)
  centralHi := (34582235686203802623/20000000000000000000)
  directionLo := (89985830266868501771/50000000000000000000)
  directionHi := (179971660533737003543/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree014.table
  base := (-3485848277378784108615256854199258520429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-1826836996990547251564773747568600000000000000)
      constant := (3113456339562678483041309073255605841278148882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree014.table
  base := (-3576369604125051288431892522679219834499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-3669252714229273941586306766651200000000000000)
      constant := (6283468797934151735210362402858621857304969884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89985830266868501771/50000000000000000000)
  centralHi := (179971660533737003543/100000000000000000000)
  directionLo := (93382709272297358089/50000000000000000000)
  directionHi := (186765418544594716179/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree015.table
  base := (-2825612497447841249631462317141575714779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-2014004193115103076452410138186800000000000000)
      constant := (3835986883131595022371202983407253702700042364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree015.table
  base := (-716718674693761365647315779703147324327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-4044699872210398408394205210138600000000000000)
      constant := (7742869116181306352617702601008409516821487456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93382709272297358089/50000000000000000000)
  centralHi := (186765418544594716179/100000000000000000000)
  directionLo := (96660287260338486019/50000000000000000000)
  directionHi := (193320574520676972039/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree016.table
  base := (-748323250801328417736179547368609178207/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-2201171389239658901340046528805000000000000000)
      constant := (4674635265677222773563394436650242083629480060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree016.table
  base := (-3779191695130290035305031366622514343713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-4420147030191522875202103653626000000000000000)
      constant := (9435449979123796410035113309216691603840173416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96660287260338486019/50000000000000000000)
  centralHi := (193320574520676972039/100000000000000000000)
  directionLo := (39932126165217695827/20000000000000000000)
  directionHi := (6239394713315264973/3125000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree017.table
  base := (-902441392949741297724501186597878747821/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-2388338585364214726227682919423200000000000000)
      constant := (5625830333227772952316290785789258621504096180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree017.table
  base := (-454636320788085315587725904209890119883/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-4795594188172647342010002097113400000000000000)
      constant := (11354083899493436994601983076805411142271248560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39932126165217695827/20000000000000000000)
  centralHi := (6239394713315264973/3125000000000000000)
  directionLo := (205805467543354075021/100000000000000000000)
  directionHi := (102902733771677037511/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree018.table
  base := (-2061868736484893980233907987432161229093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-2575505781488770551115319310041400000000000000)
      constant := (6686669839561366305698437780275647610537376970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree018.table
  base := (-10371306705224159695980299103682244967999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-5171041346153771808817900540600800000000000000)
      constant := (13492974139728367978405914294347509985792455884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205805467543354075021/100000000000000000000)
  centralHi := (102902733771677037511/50000000000000000000)
  directionLo := (42354415797933297511/20000000000000000000)
  directionHi := (52943019747416621889/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree019.table
  base := (-5683333189048191802843451218078982238051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-2762672977613326376002955700659600000000000000)
      constant := (7854749298716096338421587497519078145947045916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree019.table
  base := (-11422742679900881948320734070013349013031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-5546488504134896275625798984088200000000000000)
      constant := (15847316124794960492881411677166353914296303596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42354415797933297511/20000000000000000000)
  centralHi := (52943019747416621889/25000000000000000000)
  directionLo := (217575128193625377759/100000000000000000000)
  directionHi := (1359844551210158611/625000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree020.table
  base := (-12220421961334702574862936282922018538971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-2949840173737882200890592091277800000000000000)
      constant := (9128050749643752627636285454784959919801696318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree020.table
  base := (-1533882015150567299793516890744127031433/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-5921935662116020742433697427575600000000000000)
      constant := (18413076981942530631838557173486503819639217824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217575128193625377759/100000000000000000000)
  centralHi := (1359844551210158611/625000000000000000)
  directionLo := (111613685739405957607/50000000000000000000)
  directionHi := (44645474295762383043/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree021.table
  base := (-6445478203741972448507393196467828092739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-3137007369862438025778228481896000000000000000)
      constant := (10504866310481965635973013873577845148478605724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree021.table
  base := (-64682883977779146548762908858177619257/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-6297382820097145209241595871063000000000000000)
      constant := (21186843668665305552208005476507416713731562400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111613685739405957607/50000000000000000000)
  centralHi := (44645474295762383043/20000000000000000000)
  directionLo := (114369994257897978033/50000000000000000000)
  directionHi := (228739988515795956067/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree022.table
  base := (-669779122961591579297466143377231041031/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-3324174565986993850665864872514200000000000000)
      constant := (11983742714984042686090796463850569439075515960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree022.table
  base := (-3359150111947753188834879272869369892973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-6672829978078269676049494314550400000000000000)
      constant := (24165712506137194903694887579444894819552483472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114369994257897978033/50000000000000000000)
  centralHi := (228739988515795956067/100000000000000000000)
  directionLo := (14632677647546453987/6250000000000000000)
  directionHi := (234122842360743263793/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree023.table
  base := (-6874541133538445045629145650326395295413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-3511341762111549675553501263132400000000000000)
      constant := (13563439119872836386816002916959653452224883908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree023.table
  base := (-13785890495465943171061326701796084375839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-7048277136059394142857392758037800000000000000)
      constant := (27347204952765251620173773175489141170646645324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14632677647546453987/6250000000000000000)
  centralHi := (234122842360743263793/100000000000000000000)
  directionLo := (239384686820064609993/100000000000000000000)
  directionHi := (119692343410032304997/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree024.table
  base := (-13964104455951842266958296207899538515291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-3698508958236105500441137653750600000000000000)
      constant := (15242893774274244200278771416653296937949442878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree024.table
  base := (-13997075059740977831408761222670900498833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-7423724294040518609665291201525200000000000000)
      constant := (30729200949056590280974057087538718540653920628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239384686820064609993/100000000000000000000)
  centralHi := (119692343410032304997/50000000000000000000)
  directionLo := (244533333623061274381/100000000000000000000)
  directionHi := (122266666811530637191/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree025.table
  base := (-7025743323624993580395561665256153508133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-3885676154360661325328774044368800000000000000)
      constant := (17021196946573269817813560984241385924440599428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree025.table
  base := (-14080969863651595192290644730223164112571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-7799171452021643076473189645012600000000000000)
      constant := (34309884708165122621003942294398089316125130236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244533333623061274381/100000000000000000000)
  centralHi := (122266666811530637191/50000000000000000000)
  directionLo := (249575788532610598919/100000000000000000000)
  directionHi := (6239394713315264973/2500000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree026.table
  base := (-14020522569395411754897261601755621249821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-4072843350485217150216410434987000000000000000)
      constant := (18897568502618538529965534697687829641047525618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree026.table
  base := (-14046845861190225797210290329754230946107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-8174618610002767543281088088500000000000000000)
      constant := (38087699785250783430897918578696840691843772412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249575788532610598919/100000000000000000000)
  centralHi := (6239394713315264973/2500000000000000000)
  directionLo := (254518363169617564421/100000000000000000000)
  directionHi := (127259181584808782211/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree027.table
  base := (-13879186176827144658114112869816224603563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-4260010546609772975104046825605200000000000000)
      constant := (20871339092726529397251663371052136474327714654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree027.table
  base := (-13902653879064493527216480376384862143681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-8550065767983892010088986531987400000000000000)
      constant := (42061311363722589983009992163527878803870258996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254518363169617564421/100000000000000000000)
  centralHi := (127259181584808782211/50000000000000000000)
  directionLo := (259366767646528519671/100000000000000000000)
  directionHi := (32420845955816064959/12500000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree028.table
  base := (-3408580325487837893378357882636666812939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-4447177742734328799991683216223400000000000000)
      constant := (22941934231917404058224697796837651657553097848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree028.table
  base := (-3413803682908822166174844207430712378453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-8925512925965016476896884975474800000000000000)
      constant := (46229574337982378573171373098464409132223186192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259366767646528519671/100000000000000000000)
  centralHi := (32420845955816064959/12500000000000000000)
  directionLo := (264126187888053402359/100000000000000000000)
  directionHi := (6603154697201335059/2500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree029.table
  base := (-13291803017596017629752508819591333542037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-4634344938858884624879319606841600000000000000)
      constant := (25108860754827835785214887634141914279814330146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree029.table
  base := (-665519048136137009005106874886833463049/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-9300960083946140943704783418962200000000000000)
      constant := (50591506159563450669308182278073452017789633680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264126187888053402359/100000000000000000000)
  centralHi := (6603154697201335059/2500000000000000000)
  directionLo := (268801350623731543759/100000000000000000000)
  directionHi := (3360016882796644297/1250000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree030.table
  base := (-12856675404794740356522678070582612599029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-4821512134983440449766955997459800000000000000)
      constant := (27371695251207702334384882980273154333212307682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree030.table
  base := (-1609146863263633325340823951846050682079/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-9676407241927265410512681862449600000000000000)
      constant := (55146263658981112295847111403176721018318793312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268801350623731543759/100000000000000000000)
  centralHi := (3360016882796644297/1250000000000000000)
  directionLo := (136698289186449986231/50000000000000000000)
  directionHi := (273396578372899972463/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree031.table
  base := (-12333269431867570934387485311871300535699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-5008679331107996274654592388078000000000000000)
      constant := (29730074170914281969535818654519549290432354542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree031.table
  base := (-1543488347211278420230061803389312844181/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-10051854399908389877320580305937000000000000000)
      constant := (59893123219949886199964972652004983819740135968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136698289186449986231/50000000000000000000)
  centralHi := (273396578372899972463/100000000000000000000)
  directionLo := (277915836243414188639/100000000000000000000)
  directionHi := (1736973976521338679/625000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree032.table
  base := (-11725303953412359976040998782055520883327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-5195846527232552099542228778696200000000000000)
      constant := (32183685345854921914536929180796695466011764966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree032.table
  base := (-5869137909458765835424230771757672523083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-10427301557889514344128478749424400000000000000)
      constant := (64831463799017960785678545537700469812269467256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277915836243414188639/100000000000000000000)
  centralHi := (1736973976521338679/625000000000000000)
  directionLo := (282362771986221983407/100000000000000000000)
  directionHi := (17647673249138873963/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree033.table
  base := (-11035972320016705761347078955299149827409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-5383013723357107924429865169314400000000000000)
      constant := (34732260719794597994579882383182328765187633722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree033.table
  base := (-11047456994290558867762344734700381967861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-10802748715870638810936377192911800000000000000)
      constant := (69960752370445288675405048337586036073707623876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282362771986221983407/100000000000000000000)
  centralHi := (17647673249138873963/6250000000000000000)
  directionLo := (28674075045694178529/10000000000000000000)
  directionHi := (286740750456941785291/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree034.table
  base := (-10268016688104178456081943834932614985933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-5570180919481663749317501559932600000000000000)
      constant := (37375570110638802882809090970040886432850812114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree034.table
  base := (-1027817534365198597810789951958803623609/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-11178195873851763277744275636399200000000000000)
      constant := (75280531443642921879391115112123582124540266440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28674075045694178529/10000000000000000000)
  centralHi := (286740750456941785291/100000000000000000000)
  directionLo := (291052883410347156819/100000000000000000000)
  directionHi := (14552644170517357841/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree035.table
  base := (-2355947949431864403812442593918573849171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-5757348115606219574205137950550800000000000000)
      constant := (40113415856798034552018394319439398295811551672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree035.table
  base := (-9432769767150259011496556768352865412193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-11553643031832887744552174079886600000000000000)
      constant := (80790408354698338687759140401104722543139390388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291052883410347156819/100000000000000000000)
  centralHi := (14552644170517357841/5000000000000000000)
  directionLo := (29530205537778451057/10000000000000000000)
  directionHi := (295302055377784510571/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree036.table
  base := (-4252659861138789301369161701059852015711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-5944515311730775399092774341169000000000000000)
      constant := (42945628221387702711692325676471667804194374476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree036.table
  base := (-2128311938850361884988853222810690076701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-11929090189814012211360072523374000000000000000)
      constant := (86490046078056950876478927150791400428652517264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29530205537778451057/10000000000000000000)
  centralHi := (295302055377784510571/100000000000000000000)
  directionLo := (299490946239132718703/100000000000000000000)
  directionHi := (18718184139945794919/6250000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree037.table
  base := (-23482302731521289600312319592812904507/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-6131682507855331223980410731787200000000000000)
      constant := (45872061446483811848265194570964081734359489920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree037.table
  base := (-3760666177962271201387414212852592436963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-12304537347795136678167970966861400000000000000)
      constant := (92379155341609080187487052472714785742625807416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299490946239132718703/100000000000000000000)
  centralHi := (18718184139945794919/6250000000000000000)
  directionLo := (60724410198231833929/20000000000000000000)
  directionHi := (151811025495579584823/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree038.table
  base := (-6452334364500473592089098798590045051839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-6318849703979887048868047122405400000000000000)
      constant := (48892590365217813633360213129387554438258530662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree038.table
  base := (-6458502480189928954507779331789539233541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-12679984505776261144975869410348800000000000000)
      constant := (98457487859781432445919744550797944995316202756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60724410198231833929/20000000000000000000)
  centralHi := (151811025495579584823/50000000000000000000)
  directionLo := (153848848563244887123/50000000000000000000)
  directionHi := (307697697126489774247/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree039.table
  base := (-5320592659656380159727928851421713547923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-6506016900104442873755683513023600000000000000)
      constant := (52007107492701167281517749223161008521360247534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree039.table
  base := (-1331506874281200512892496909389506205091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-13055431663757385611783767853836200000000000000)
      constant := (104724830525841034470502506308081683561058010224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153848848563244887123/50000000000000000000)
  centralHi := (307697697126489774247/100000000000000000000)
  directionLo := (311720059966971018867/100000000000000000000)
  directionHi := (77930014991742754717/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree040.table
  base := (-2060105669550511906967639291480753690493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-6693184096228998698643319903641800000000000000)
      constant := (55215520528027581208372077068361045147425273188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree040.table
  base := (-515624615478505323379956380427387833829/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-13430878821738510078591666297323600000000000000)
      constant := (111181000427299257741381797601830627367243617312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311720059966971018867/100000000000000000000)
  centralHi := (77930014991742754717/25000000000000000000)
  directionLo := (315691176238232833199/100000000000000000000)
  directionHi := (789227940595582083/250000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree041.table
  base := (-178258415608810506039299915493266743069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-6880351292353554523530956294260000000000000000)
      constant := (58517750209223224657087545233732277248852832032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree041.table
  base := (-2856345908801034266301030219281400672419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-13806325979719634545399564740811000000000000000)
      constant := (117825840567685095956562887213737836329511608604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315691176238232833199/100000000000000000000)
  centralHi := (789227940595582083/250000000000000000)
  directionLo := (319612956125914828613/100000000000000000000)
  directionHi := (159806478062957414307/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree042.table
  base := (-379293362368966602992366926955087241147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-7067518488478110348418592684878200000000000000)
      constant := (61913728471254284921612072848462144267214554104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree042.table
  base := (-760438552090280251950038243862010056861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-14181773137700759012207463184298400000000000000)
      constant := (124659216194547217369278142651963440607227895752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319612956125914828613/100000000000000000000)
  centralHi := (159806478062957414307/50000000000000000000)
  directionLo := (323487194016104649471/100000000000000000000)
  directionHi := (1263621851625408787/390625000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree043.table
  base := (-58012025362485371661592810079880596741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-7254685684602666173306229075496400000000000000)
      constant := (65403396864263665151957959546719599325896733956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree043.table
  base := (-7454964923999500326703863075777528877/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-14557220295681883479015361627785800000000000000)
      constant := (131681011647760046516023789921896653645472219712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323487194016104649471/100000000000000000000)
  centralHi := (1263621851625408787/390625000000000000)
  directionLo := (163657789045679022259/50000000000000000000)
  directionHi := (327315578091358044519/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree044.table
  base := (1350715598109039248825423351761034173319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-7441852880727221998193865466114600000000000000)
      constant := (68986705195266547612064804998592324730576743498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree044.table
  base := (1347855768825502366414837368503600537577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-14932667453663007945823260071273200000000000000)
      constant := (138891127654397924355353139279183458472650577068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163657789045679022259/50000000000000000000)
  centralHi := (327315578091358044519/100000000000000000000)
  directionLo := (41387462365987661669/12500000000000000000)
  directionHi := (331099698927901293353/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree045.table
  base := (1441266008562482558628584828629765558551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-7629020076851777823081501856732800000000000000)
      constant := (72663610361733065901876135994816929561031776084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree045.table
  base := (72000524508031495415098378346852818991/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-15308114611644132412631158514760600000000000000)
      constant := (146289479006896417430687399675849196546539401760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41387462365987661669/12500000000000000000)
  centralHi := (331099698927901293353/100000000000000000000)
  directionLo := (334841057218217872821/100000000000000000000)
  directionHi := (167420528609108936411/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree046.table
  base := (895796852480206506303138551775718958963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-7816187272976333647969138247351000000000000000)
      constant := (76434075349948538440544784719158187004266360730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree046.table
  base := (4476780567140714904617534267490374452903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-15683561769625256879439056958248000000000000000)
      constant := (153875992570189928005576315388710654024651167252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334841057218217872821/100000000000000000000)
  centralHi := (167420528609108936411/50000000000000000000)
  directionLo := (338541070725371266579/100000000000000000000)
  directionHi := (16927053536268563329/5000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree047.table
  base := (191865427473333294986057777000256290491/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17860000000000000000000000000000000000000000
      center := (101115)
      previous := (89987)
      next := (0)
      square := (4228509781648704723977516553800000000000000)
      linear := (-170284137640444456869293077403600000000000000)
      constant := (1708469539890904993470421485688868647514141632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree047.table
  base := (1534440155476136576120475307971400555141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35720000000000000000000000000000000000000000
      center := (201695)
      previous := (180509)
      next := (0)
      square := (8457019563297409447955033107600000000000000)
      linear := (-341681041012901730771211817058200000000000000)
      constant := (3439374586621531619117661960352420371131854608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338541070725371266579/100000000000000000000)
  centralHi := (16927053536268563329/5000000000000000000)
  directionLo := (342201080560462001241/100000000000000000000)
  directionHi := (171100540280231000621/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree048.table
  base := (491520943899497960699921023304897445017/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-8190521665225445297744411028587400000000000000)
      constant := (84255562141507151610071957613384955221273872224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree048.table
  base := (982830026677499443947543125358921945509/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-16434456085587505813054853845222800000000000000)
      constant := (169613264130750226647475081363503658015198663648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342201080560462001241/100000000000000000000)
  centralHi := (171100540280231000621/50000000000000000000)
  directionLo := (86455589215509506557/25000000000000000000)
  directionHi := (345822356862038026229/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree049.table
  base := (9652629300723155410193139441456946042037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-8377688861350001122632047419205600000000000000)
      constant := (88306533210609053425874764864802828964660669854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree049.table
  base := (1930228776145857677553336711839668666297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-16809903243568630279862752288710200000000000000)
      constant := (177763922003317214678856609447074929671863027740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86455589215509506557/25000000000000000000)
  centralHi := (345822356862038026229/100000000000000000000)
  directionLo := (349406103945654838487/100000000000000000000)
  directionHi := (43675762993206854811/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree050.table
  base := (2876084121865479195568023166204124948089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-8564856057474556947519683809823800000000000000)
      constant := (92450961454004889209620881855610026625569947352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree050.table
  base := (11503035190646213219974359013041151264087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-17185350401549754746670650732197600000000000000)
      constant := (186102539495563916245584310382837900638819981908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349406103945654838487/100000000000000000000)
  centralHi := (43675762993206854811/12500000000000000000)
  directionLo := (352953464982777479259/100000000000000000000)
  directionHi := (17647673249138873963/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree051.table
  base := (13419250748494275696630923075590837164123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-8752023253599112772407320200442000000000000000)
      constant := (96688829586852103605478582727579896053230812866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree051.table
  base := (13418111208098784571422443786504247205809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-17560797559530879213478549175685000000000000000)
      constant := (194629082537938706137874294925305154037900038156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352953464982777479259/100000000000000000000)
  centralHi := (17647673249138873963/5000000000000000000)
  directionLo := (11139547695642399703/3125000000000000000)
  directionHi := (356465526260556790497/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree052.table
  base := (1924649407157149190539319762279930313783/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-8939190449723668597294956591060200000000000000)
      constant := (101020122765975342024856120778576415283196580688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree052.table
  base := (3079239549989181530374358938802072150971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-17936244717512003680286447619172400000000000000)
      constant := (203343521887879124797962054759909235404968076820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11139547695642399703/3125000000000000000)
  centralHi := (356465526260556790497/100000000000000000000)
  directionLo := (71988664213494801417/20000000000000000000)
  directionHi := (179971660533737003543/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree053.table
  base := (17438018165684158068824250553343329975873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-9126357645848224422182592981678400000000000000)
      constant := (105444828244944205300954998172864795804834731366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree053.table
  base := (8718572655630357434862921336617916535277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-18311691875493128147094346062659800000000000000)
      constant := (212245832445900029987099991486190999599216887736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71988664213494801417/20000000000000000000)
  centralHi := (179971660533737003543/50000000000000000000)
  directionLo := (363387833244248357777/100000000000000000000)
  directionHi := (181693916622124178889/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree054.table
  base := (19541589075619731295651967352083141105047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-9313524841972780247070229372296600000000000000)
      constant := (109962935077876729654282541596903363030639855274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree054.table
  base := (19540825568801517608932837734644822641203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-18687139033474252613902244506147200000000000000)
      constant := (221335992668582314053670873108907211404295724452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363387833244248357777/100000000000000000000)
  centralHi := (181693916622124178889/50000000000000000000)
  directionLo := (366800000434591911571/100000000000000000000)
  directionHi := (91700000108647977893/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree055.table
  base := (10853898004351281824274664489983030193743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-9500692038097336071957865762914800000000000000)
      constant := (114574433865085306680388149577486561041046349812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree055.table
  base := (5426782094972763431280512082644899716461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-19062586191455377080710142949634600000000000000)
      constant := (230613984064732747519829163732910900375993354096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366800000434591911571/100000000000000000000)
  centralHi := (91700000108647977893/25000000000000000000)
  directionLo := (46272589633281345743/12500000000000000000)
  directionHi := (74036143413250153189/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree056.table
  base := (5984135701075069048932447146667355109283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-9687859234221891896845502153533000000000000000)
      constant := (119279316534654133226979795798904604490333734344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree056.table
  base := (23935959206511697059754145502807377473783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-19438033349436501547518041393122000000000000000)
      constant := (240079790762930779235574646655378113759808585172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46272589633281345743/12500000000000000000)
  centralHi := (74036143413250153189/20000000000000000000)
  directionLo := (373530837089189432357/100000000000000000000)
  directionHi := (186765418544594716179/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree057.table
  base := (26227746885027080313407958043905756494423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-9875026430346447721733138544151200000000000000)
      constant := (124077576154872291425399687210892787011654855466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree057.table
  base := (13113618452184778015793160486912057531541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-19813480507417626014325939836609400000000000000)
      constant := (249733399140347773506681954251448362733250458488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373530837089189432357/100000000000000000000)
  centralHi := (186765418544594716179/50000000000000000000)
  directionLo := (37685117649467083787/10000000000000000000)
  directionHi := (376851176494670837871/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree058.table
  base := (14290668668958614308059774026037451555187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-10062193626471003546620774934769400000000000000)
      constant := (128969206773163610508617180441064071516891014308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree058.table
  base := (28580891825216541423629167169417733357861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-20188927665398750481133838280096800000000000000)
      constant := (259574797504157248123046036819932626747051136124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37685117649467083787/10000000000000000000)
  centralHi := (376851176494670837871/100000000000000000000)
  directionLo := (19007125781814338063/5000000000000000000)
  directionHi := (380142515636286761261/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree059.table
  base := (30997253266662887968636586991557092420989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-10249360822595559371508411325387600000000000000)
      constant := (133954203277770218347594969095724335452002658638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree059.table
  base := (15498432094023091677676975868141967553257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-20564374823379874947941736723584200000000000000)
      constant := (269603975818084712895244208658428767161421996376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19007125781814338063/5000000000000000000)
  centralHi := (380142515636286761261/100000000000000000000)
  directionLo := (191702800685821684309/50000000000000000000)
  directionHi := (383405601371643368619/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree060.table
  base := (16737721188312133524759692132815942714821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-10436528018720115196396047716005800000000000000)
      constant := (139032561278975461579228762666803671726735008764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree060.table
  base := (33475102681067588223579425739107673774019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-20939821981360999414749635167071600000000000000)
      constant := (279820925467701465441599988970680352703877405796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191702800685821684309/50000000000000000000)
  centralHi := (383405601371643368619/100000000000000000000)
  directionLo := (96660287260338486019/25000000000000000000)
  directionHi := (386641149041353944077/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree061.table
  base := (4501982469966150680922494553359517916263/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-10623695214844671021283684106624000000000000000)
      constant := (144204277007105946914265831047758487223415589968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree061.table
  base := (18007781630879765630883137006094238063713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-21315269139342123881557533610559000000000000000)
      constant := (290225639058972872463407691369408925126176786584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96660287260338486019/25000000000000000000)
  centralHi := (386641149041353944077/100000000000000000000)
  directionLo := (38984984430019392849/10000000000000000000)
  directionHi := (389849844300193928491/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree062.table
  base := (1544738674040985869727590483144384664137/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-10810862410969226846171320497242200000000000000)
      constant := (149469347224942384890780080416668648436924701350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree062.table
  base := (7723641625387904467174987993501471321699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-21690716297323248348365432054046400000000000000)
      constant := (300818110245349444787004218936391505056860574580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38984984430019392849/10000000000000000000)
  centralHi := (389849844300193928491/100000000000000000000)
  directionLo := (393032344813696501243/100000000000000000000)
  directionHi := (98258086203424125311/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree063.table
  base := (10320807633157856003522071946028114092773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-10998029607093782671058956887860400000000000000)
      constant := (154827769152503762478932753554629017812702204664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree063.table
  base := (10320751207189779403992907404899317125113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-22066163455304372815173330497533800000000000000)
      constant := (311598333579356594268444966602171942824929883568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393032344813696501243/100000000000000000000)
  centralHi := (98258086203424125311/25000000000000000000)
  directionLo := (396189281832080103539/100000000000000000000)
  directionHi := (19809464091604005177/5000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree064.table
  base := (22005061182139641269092111614717170084501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-11185196803218338495946593278478600000000000000)
      constant := (160279540402456913956858850091265977382466365884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree064.table
  base := (44009925515949781199817110492623385666273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-22441610613285497281981228941021200000000000000)
      constant := (322566304385211954026318403061777184479196576332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396189281832080103539/100000000000000000000)
  centralHi := (19809464091604005177/5000000000000000000)
  directionLo := (399321261652176958271/100000000000000000000)
  directionHi := (6239394713315264973/1562500000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree065.table
  base := (1169977948063516392092139626586668226817/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-11372363999342894320834229669096800000000000000)
      constant := (165824658924650482526352487360120774171818904560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree065.table
  base := (46798946282573054708524278851529360517519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-22817057771266621748789127384508600000000000000)
      constant := (333722018649490951914143445791751030161123159796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399321261652176958271/100000000000000000000)
  centralHi := (6239394713315264973/1562500000000000000)
  directionLo := (201214433488476011671/50000000000000000000)
  directionHi := (402428866976952023343/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree066.table
  base := (49650196233407755136900805063298712615799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-11559531195467450145721866059715000000000000000)
      constant := (171463122958484306420785767741425820534395399658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree066.table
  base := (49650046609043185207328698839317266801321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-23192504929247746215597025827996000000000000000)
      constant := (345065472927283453386220102242677240019672974764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201214433488476011671/50000000000000000000)
  centralHi := (402428866976952023343/100000000000000000000)
  directionLo := (405512658181246324087/100000000000000000000)
  directionHi := (50689082272655790511/12500000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree067.table
  base := (2102533571401069523372156366191506434531/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-11746698391592005970609502450333200000000000000)
      constant := (177194930992007350366705693919449435828185030050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree067.table
  base := (26281604441174250354189845561692881995267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-23567952087228870682404924271483400000000000000)
      constant := (356596664261646606902540048965481370601786810056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405512658181246324087/100000000000000000000)
  centralHi := (50689082272655790511/12500000000000000000)
  directionLo := (408573174491531315787/100000000000000000000)
  directionHi := (102143293622882828947/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree068.table
  base := (43389477819738657366316525503862260541/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-11933865587716561795497138840951400000000000000)
      constant := (183020081726793667687103073905172663519145756160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree068.table
  base := (27769208992125091957148730436421439204483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-23943399245209995149212822714970800000000000000)
      constant := (368315590114470006859949976484773953798810847944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408573174491531315787/100000000000000000000)
  centralHi := (102143293622882828947/25000000000000000000)
  directionLo := (205805467543354075021/50000000000000000000)
  directionHi := (411610935086708150043/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree069.table
  base := (58575759922391115159588326286948281246383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-12121032783841117620384775231569600000000000000)
      constant := (188938574047780153807509827381999062624383881786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree069.table
  base := (29287830468913501496846466196554533992841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-24318846403191119616020721158458200000000000000)
      constant := (380222248307136209173668961216646197769708236888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205805467543354075021/50000000000000000000)
  centralHi := (411610935086708150043/100000000000000000000)
  directionLo := (10365661003157892107/2500000000000000000)
  directionHi := (414626440126315684281/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree070.table
  base := (61675012816507116999950813800313888504063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-12308199979965673445272411622187800000000000000)
      constant := (194950406997365158854995129414111948428808056346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree070.table
  base := (61674926604099198871075582952240474536163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-24694293561172244082828619601945600000000000000)
      constant := (392316636969588735971067352242768439827029189092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10365661003157892107/2500000000000000000)
  centralHi := (414626440126315684281/100000000000000000000)
  directionLo := (104405042927978405781/25000000000000000000)
  directionHi := (668192274739061797/160000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree071.table
  base := (64836280494579370520978561468643647396399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-12495367176090229270160048012806000000000000000)
      constant := (201055579753166045028276361144449535049748524858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree071.table
  base := (64836205421636018908034884237812673726731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-25069740719153368549636518045433000000000000000)
      constant := (404598754496616346776198236427937617915938507204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104405042927978405781/25000000000000000000)
  centralHi := (668192274739061797/160000000000000000)
  directionLo := (420592594786873529097/100000000000000000000)
  directionHi := (210296297393436764549/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree072.table
  base := (68059554542893551611920262453956506656367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-12682534372214785095047684403424200000000000000)
      constant := (207254091608918804532848836374418017081748758714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree072.table
  base := (68059489183056721904884806438160239344031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-25445187877134493016444416488920400000000000000)
      constant := (417068599510331133233493524343252093622033300404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420592594786873529097/100000000000000000000)
  centralHi := (210296297393436764549/50000000000000000000)
  directionLo := (42354415797933297511/10000000000000000000)
  directionHi := (423544157979332975111/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree073.table
  base := (2229525866739252303354223244860626870363/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-12869701568339340919935320794042400000000000000)
      constant := (213545941958075872125236325743506953704064350272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree073.table
  base := (2229524088849930392300035451161277614497/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-25820635035115617483252314932407800000000000000)
      constant := (429726170827962860381300878658156792793030859136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42354415797933297511/10000000000000000000)
  centralHi := (423544157979332975111/100000000000000000000)
  directionLo := (426475294392640220679/100000000000000000000)
  directionHi := (10661882359816005517/2500000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree074.table
  base := (37346046933598902603395862014489085606301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-13056868764463896744822957184660600000000000000)
      constant := (219931130279720969560635409824557285647928237084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree074.table
  base := (74692044354459576797586243239934194468391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-26196082193096741950060213375895200000000000000)
      constant := (442571467434216317971022463698011212304131354644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426475294392640220679/100000000000000000000)
  centralHi := (10661882359816005517/2500000000000000000)
  directionLo := (13418325698351022617/3125000000000000000)
  directionHi := (85877284469446544749/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree075.table
  base := (39050673803940616093516594520405866384189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-13244035960588452569710593575278800000000000000)
      constant := (226409656126473664645300065137330068472043186076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree075.table
  base := (39050652262740902741957632539283355242037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-26571529351077866416868111819382600000000000000)
      constant := (455604488457545168503148640962466968622908279416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13418325698351022617/3125000000000000000)
  centralHi := (85877284469446544749/20000000000000000000)
  directionLo := (86455589215509506557/20000000000000000000)
  directionHi := (216138973038773766393/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree076.table
  base := (40786292190181291323155085020968358879081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-13431203156713008394598229965897000000000000000)
      constant := (232981519114102566469859446163572651962055634604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree076.table
  base := (81572546899841980367622571382439967654307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-26946976509058990883676010262870000000000000000)
      constant := (468825233149787380640001600864574351529675676388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86455589215509506557/20000000000000000000)
  centralHi := (216138973038773766393/50000000000000000000)
  directionLo := (435150256387250755519/100000000000000000000)
  directionHi := (1359844551210158611/312500000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree077.table
  base := (85105800253333456162585051565163958953237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-13618370352837564219485866356515200000000000000)
      constant := (239646718912605785286086871385738243042452620254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree077.table
  base := (17021153530388063096760741630195813673847/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-27322423667040115350483908706357400000000000000)
      constant := (482233700868685959914649324048900844914100648740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435150256387250755519/100000000000000000000)
  centralHi := (1359844551210158611/312500000000000000)
  directionLo := (427738018814251009/97656250000000000)
  directionHi := (438003731265793033217/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree078.table
  base := (5543811990642044229510941420823242198501/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-13805537548962120044373502747133400000000000000)
      constant := (246405255238551383135046681650842713546025135072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree078.table
  base := (88700963497635771554573324511639773590597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-27697870825021239817291807149844800000000000000)
      constant := (495829891062886172088963306269560231749483786748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427738018814251009/97656250000000000)
  centralHi := (438003731265793033217/100000000000000000000)
  directionLo := (440838736469044897929/100000000000000000000)
  directionHi := (44083873646904489793/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree079.table
  base := (9235815627108815587526577114011139788057/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-13992704745086675869261139137751600000000000000)
      constant := (253257127848499822134069853873874280960890806940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree079.table
  base := (92358131617543292915959022736374383921227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-28073317983002364284099705593332200000000000000)
      constant := (509613803259058376477853205506376952070231273668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440838736469044897929/100000000000000000000)
  centralHi := (44083873646904489793/10000000000000000000)
  directionLo := (110913906516634274193/25000000000000000000)
  directionHi := (443655626066537096773/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree080.table
  base := (96077291024827231822563738826468513914581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-14179871941211231694148775528369800000000000000)
      constant := (260202336533355561740414798285635419995017758302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree080.table
  base := (12009658698899790606573578636871296111223/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-28448765140983488750907604036819600000000000000)
      constant := (523585437050845301777483479744828005410692497056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110913906516634274193/25000000000000000000)
  centralHi := (443655626066537096773/100000000000000000000)
  directionLo := (446454742957623830429/100000000000000000000)
  directionHi := (44645474295762383043/10000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree081.table
  base := (49929196985946456333569258820490250961591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-14367039137335787519036411918988000000000000000)
      constant := (267240881113516548662264479207412835292435743444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree081.table
  base := (49929187670274440156135363183505164786597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-28824212298964613217715502480307000000000000000)
      constant := (537744792089375268193584025096280837170066101496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446454742957623830429/100000000000000000000)
  centralHi := (44645474295762383043/10000000000000000000)
  directionLo := (224618209679349539027/50000000000000000000)
  directionHi := (89847283871739815611/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree082.table
  base := (103701463274422177140821643082222563181321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-14554206333460343343924048309606200000000000000)
      constant := (274372761434708885168326299392027926398566447382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree082.table
  base := (103701447081453583505708879653973072506629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-29199659456945737684523400923794400000000000000)
      constant := (552091868075119484993144598884232115304702903036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224618209679349539027/50000000000000000000)
  centralHi := (89847283871739815611/20000000000000000000)
  directionLo := (226000488631712870873/50000000000000000000)
  directionHi := (452000977263425741747/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree083.table
  base := (53803248676836953172473173081796009433049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-14741373529584899168811684700224400000000000000)
      constant := (281597977364409884256008372917207291247657998316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree083.table
  base := (26901620820512841589217814438742644939579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-29575106614926862151331299367281800000000000000)
      constant := (566626664750902988623288673159351955812145123344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226000488631712870873/50000000000000000000)
  centralHi := (452000977263425741747/100000000000000000000)
  directionLo := (227374364438891224417/50000000000000000000)
  directionHi := (90949745775556489767/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree084.table
  base := (111573494853436044078552577623083288733407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-14928540725709454993699321090842600000000000000)
      constant := (288916528788776393503689711327799657422859650394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree084.table
  base := (111573482627029211686186907545289395537599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-29950553772907986618139197810769200000000000000)
      constant := (581349181895905768507841158027250964880434270516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227374364438891224417/50000000000000000000)
  centralHi := (90949745775556489767/20000000000000000000)
  directionLo := (114369994257897978033/25000000000000000000)
  directionHi := (457479977031591912133/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree085.table
  base := (115602454608601710589984494273616117158357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-15115707921834010818586957481460800000000000000)
      constant := (296328415610007011211256819834995134106506803294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree085.table
  base := (115602443986952283393422388154635643416441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-30326000930889111084947096254256600000000000000)
      constant := (596259419320513786622950462500860725359325780844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114369994257897978033/25000000000000000000)
  centralHi := (457479977031591912133/100000000000000000000)
  directionLo := (46019501556806635847/10000000000000000000)
  directionHi := (460195015568066358471/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree086.table
  base := (59846687809092041502229369274461130482371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-15302875117958566643474593872079000000000000000)
      constant := (303833637744076901492954633837966032429902372964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree086.table
  base := (23938673278387837034462168034991891349001/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-30701448088870235551754994697744000000000000000)
      constant := (611357376861899474631135281155320193436178419420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46019501556806635847/10000000000000000000)
  centralHi := (460195015568066358471/100000000000000000000)
  directionLo := (462894129712788443137/100000000000000000000)
  directionHi := (231447064856394221569/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree087.table
  base := (123846257022143006215097102031396801053367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-15490042314083122468362230262697200000000000000)
      constant := (311432195118792573648801582765721760274021732714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree087.table
  base := (61923124504533357354894978646661819860607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-31076895246851360018562893141231400000000000000)
      constant := (626643054380228353635269461757588220930956291176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462894129712788443137/100000000000000000000)
  centralHi := (231447064856394221569/50000000000000000000)
  directionLo := (232788798211719579279/50000000000000000000)
  directionHi := (465577596423439158559/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree088.table
  base := (1600763726018560960664743746938462450699/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-15677209510207678293249866653315400000000000000)
      constant := (319124087672121426624820565246049473202926036640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree088.table
  base := (64030545561487853403222138451718533975239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-31452342404832484485370791584718800000000000000)
      constant := (642116451755403065545014338783470228715798048552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232788798211719579279/50000000000000000000)
  centralHi := (465577596423439158559/100000000000000000000)
  directionLo := (93649136944297305517/20000000000000000000)
  directionHi := (234122842360743263793/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree089.table
  base := (5293515926446936342697215222576111476261/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-15864376706332234118137503043933600000000000000)
      constant := (326909315350757244472112808963849148738507521550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree089.table
  base := (132337892119224426534119295377522049213353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-31827789562813608952178690028206200000000000000)
      constant := (657777568884268674133691621545920386710134555052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93649136944297305517/20000000000000000000)
  centralHi := (234122842360743263793/50000000000000000000)
  directionLo := (9417973120139189191/2000000000000000000)
  directionHi := (470898656006959459551/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree090.table
  base := (27335331343090841387807821538605171094023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-16051543902456789943025139434551800000000000000)
      constant := (334787878108888311814374511447679976359872393330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree090.table
  base := (136676651470000233495832138179898886209077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-32203236720794733418986588471693600000000000000)
      constant := (673626405678213882080894237136390644612324683068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9417973120139189191/2000000000000000000)
  centralHi := (470898656006959459551/100000000000000000000)
  directionLo := (473536764357349249799/100000000000000000000)
  directionHi := (2367683821786746249/500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree091.table
  base := (141077373275252174919958360274413359500433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-16238711098581345767912775825170000000000000000)
      constant := (342759775907139526855198484489363456223185346886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree091.table
  base := (141077368721855393443196240012099703863799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-32578683878775857885794486915181000000000000000)
      constant := (689662962061112069970066055426313021683470031316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473536764357349249799/100000000000000000000)
  centralHi := (2367683821786746249/500000000000000000)
  directionLo := (476160256811606112679/100000000000000000000)
  directionHi := (11904006420290152817/2500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree092.table
  base := (145540047437348938248388550998777927195423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-16425878294705901592800412215788200000000000000)
      constant := (350825008711663932822300747130941416764638197466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree092.table
  base := (145540043485180253958439790611818652226043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-32954131036756982352602385358668400000000000000)
      constant := (705887237967554010914701873821610562610317003012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476160256811606112679/100000000000000000000)
  centralHi := (11904006420290152817/2500000000000000000)
  directionLo := (239384686820064609993/50000000000000000000)
  directionHi := (478769373640129219987/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree093.table
  base := (150064678855088844262286261726374175257773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-16613045490830457417688048606406400000000000000)
      constant := (358983576493362560919924050766927351019487981166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree093.table
  base := (1200517403401341070914683163341354500911/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-33329578194738106819410283802155800000000000000)
      constant := (722299233341330936110044048413739469878867790500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239384686820064609993/50000000000000000000)
  centralHi := (478769373640129219987/100000000000000000000)
  directionLo := (481364348601585402619/100000000000000000000)
  directionHi := (24068217430079270131/5000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree094.table
  base := (154651267230397608161398198775176302294799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17860000000000000000000000000000000000000000
      center := (101115)
      previous := (89987)
      next := (0)
      square := (4228509781648704723977516553800000000000000)
      linear := (-357451333765000281756929468021800000000000000)
      constant := (7813520834621584245390756030192864875898511014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree094.table
  base := (154651264254057151847451344566740862872217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35720000000000000000000000000000000000000000
      center := (201695)
      previous := (180509)
      next := (0)
      square := (8457019563297409447955033107600000000000000)
      linear := (-717128198994026197579110260545600000000000000)
      constant := (15721254215619840036163157660086698362179559124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481364348601585402619/100000000000000000000)
  centralHi := (24068217430079270131/5000000000000000000)
  directionLo := (483945409187333451993/100000000000000000000)
  directionHi := (241972704593666725997/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree095.table
  base := (1991247653836602294110546669311201015541/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-16987379883079569067463321387642800000000000000)
      constant := (375580716891701344892299401361387916851723409760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree095.table
  base := (39824952431119538544080510728580333845101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-34080472510700355753026080689130600000000000000)
      constant := (755686382304429072852521588677341798069003745136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483945409187333451993/100000000000000000000)
  centralHi := (241972704593666725997/50000000000000000000)
  directionLo := (486512776854177370009/100000000000000000000)
  directionHi := (48651277685417737001/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree096.table
  base := (164010313864174627671818991704280145345629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-17174547079204124892350957778261000000000000000)
      constant := (384019289468313507155206311774783083960602789518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree096.table
  base := (6560412464949423779995689181237756456233/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-34455919668681480219833979132618000000000000000)
      constant := (772661535816512614407003022947657787622455524300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486512776854177370009/100000000000000000000)
  centralHi := (48651277685417737001/10000000000000000000)
  directionLo := (244533333623061274381/50000000000000000000)
  directionHi := (489066667246122548763/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree097.table
  base := (168782771712417225796994725938853631458089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-17361714275328680717238594168879200000000000000)
      constant := (392551196941125494022904620981178501531854906838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree097.table
  base := (33756553953781054291397901825704329457663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-34831366826662604686641877576105400000000000000)
      constant := (789824408639673059741793646424477603233351475460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell032.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244533333623061274381/50000000000000000000)
  centralHi := (489066667246122548763/100000000000000000000)
  directionLo := (491607290405763340749/100000000000000000000)
  directionHi := (1966429161623053363/400000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree098.table
  base := (86808592844190726963685281574669046389283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4752405)
      previous := (4229389)
      next := (0)
      square := (198739959737489122026943278028600000000000000)
      linear := (-17548881471453236542126230559497400000000000000)
      constant := (401176439296431715403716963661874538184018387172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree098.table
  base := (86808592001311879002231708860491203050497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (9479665)
      previous := (8483923)
      next := (0)
      square := (397479919474978244053886556057200000000000000)
      linear := (-35206813984643729153449776019592800000000000000)
      constant := (807175000747491607271181186611963510265859276696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell032.Kernel098
