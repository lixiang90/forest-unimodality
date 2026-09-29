import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell030.Parameters
import ForestUnimodality.BinomialMassData.Q22_47.Batch000_049
import ForestUnimodality.BinomialMassData.Q22_47.Batch050_099
import ForestUnimodality.BinomialMassData.Q22_47.Batch100_149
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch000_049
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch050_099
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree000.table
  base := (1372919485586892772182920903/25000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (178690478193712476429055868000000000000)
      linear := (12229325145131182336899478000000000000)
      constant := (109833558846951421774633672240000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree000.table
  base := (1372919485586892772182920903/25000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (178690478193712476429055868000000000000)
      linear := (12229325145131182336899478000000000000)
      constant := (109833558846951421774633672240000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree001.table
  base := (6357683720422355981739371320582375224309/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-342517329659002619473076588122000000000000)
      constant := (140515074453375534832678021451524668704985810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree001.table
  base := (79298511451704705500411625086279550326259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-620238412497337043667042577686760000000000000)
      constant := (253080224563437292167927478861059145762499653164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24949019999060795503/50000000000000000000)
  directionHi := (49898039998121591007/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree002.table
  base := (38210852058349752421285490917304532227727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-712049238563600020728364123146000000000000)
      constant := (84728426718277499167913593476269711691048943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree002.table
  base := (190299534577584540424260944218652745495911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-1289238140532972668450975914531630000000000000)
      constant := (152336558665686101199311454733533233242968731039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24949019999060795503/50000000000000000000)
  centralHi := (49898039998121591007/100000000000000000000)
  directionLo := (70566484901178720193/100000000000000000000)
  directionHi := (35283242450589360097/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree003.table
  base := (7518988971803906053011846935884374375663/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-5407905737340987109918258290850000000000000)
      constant := (269453348001495328636230244003157327933433072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree003.table
  base := (23934957208684119780371220002947930646867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-391647573713721658646981850275300000000000000)
      constant := (19355848803602217219330355152111527596413442283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70566484901178720193/100000000000000000000)
  centralHi := (35283242450589360097/50000000000000000000)
  directionLo := (21606485118712660533/25000000000000000000)
  directionHi := (86425940474850642133/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree004.table
  base := (39908405887529870232543654873368409447439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-7255565281863974116194695965970000000000000)
      constant := (182981330082766200923983829234461632938785502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree004.table
  base := (79339505696657544198720555983111081708313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-2627237596604243918018842588221370000000000000)
      constant := (65690320745565749046583612353293018997212493537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21606485118712660533/25000000000000000000)
  centralHi := (86425940474850642133/100000000000000000000)
  directionLo := (24949019999060795503/25000000000000000000)
  directionHi := (99796079996243182013/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree005.table
  base := (11160958576630972100471016065430848799521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-1820644965277392224494226728218000000000000)
      constant := (26753486670921410122050280190076744998141889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree005.table
  base := (55453537493147429139704113984036593448657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-3296237324639879542802775925066240000000000000)
      constant := (48032970251100353722230614155409478659038075993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24949019999060795503/25000000000000000000)
  centralHi := (99796079996243182013/100000000000000000000)
  directionLo := (55787704689901678031/50000000000000000000)
  directionHi := (111575409379803356063/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree006.table
  base := (159634733581876873707061106239393726197/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-10950884370909948128747571316210000000000000)
      constant := (105462241173719961259246609235402109739308288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree006.table
  base := (40606922465599535028039548980275545570001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-3965237052675515167586709261911110000000000000)
      constant := (37898128166107883789574454328184503539251727449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55787704689901678031/50000000000000000000)
  centralHi := (111575409379803356063/100000000000000000000)
  directionLo := (122224737160383588507/100000000000000000000)
  directionHi := (30556184290095897127/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree007.table
  base := (31026625036433598480843244750946006235089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-12798543915432935135024008991330000000000000)
      constant := (89284352332689947010367780373459727773311601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree007.table
  base := (123318713706694736407748845803827205567/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-926847356142230158474128519751196000000000000)
      constant := (6423987233055220366530747730169785312609929150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122224737160383588507/100000000000000000000)
  centralHi := (30556184290095897127/25000000000000000000)
  directionLo := (132017804744583580809/100000000000000000000)
  directionHi := (13201780474458358081/10000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree008.table
  base := (24134425461134987192442294430440800364557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-14646203459955922141300446666450000000000000)
      constant := (80482722218286749355983038822603728005306413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree008.table
  base := (23979061961865549232446254759312727028119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-5303236508746786417154575935600850000000000000)
      constant := (28989665655451946686813743423759034855846468431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132017804744583580809/100000000000000000000)
  centralHi := (13201780474458358081/10000000000000000000)
  directionLo := (141132969802357440387/100000000000000000000)
  directionHi := (35283242450589360097/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree009.table
  base := (19014825004694491453163870103908886862821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-16493863004478909147576884341570000000000000)
      constant := (76461625471898697335526587593554731079971589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree009.table
  base := (377739696924412430838297200891339752999/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-1194447247356484408387701854489144000000000000)
      constant := (5515165169946734040415980669641520196892995510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141132969802357440387/100000000000000000000)
  centralHi := (35283242450589360097/25000000000000000000)
  directionLo := (74847059997182386509/50000000000000000000)
  directionHi := (149694119994364773019/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree010.table
  base := (7508162124581044154334552217170020045317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-18341522549001896153853322016690000000000000)
      constant := (75781899879274190242863868738857148560210506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree010.table
  base := (3726764933768025441810282163708389100057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-6641235964818057666722442609290590000000000000)
      constant := (27362955806504077972890872446146764717805418372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74847059997182386509/50000000000000000000)
  centralHi := (149694119994364773019/100000000000000000000)
  directionLo := (39447864293062036961/25000000000000000000)
  directionHi := (31558291434449629569/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree011.table
  base := (5884840208221742848678043810440652196987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-20189182093524883160129759691810000000000000)
      constant := (77627888143602936913916263508426801406288566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree011.table
  base := (11673474496365512126993356084263587018109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-7310235692853693291506375946135460000000000000)
      constant := (28059339006868458746921719391091869454004003941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39447864293062036961/25000000000000000000)
  centralHi := (31558291434449629569/20000000000000000000)
  directionLo := (165493076447915378051/100000000000000000000)
  directionHi := (41373269111978844513/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree012.table
  base := (452947359829216993875310026878153444031/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-4407368327609574033281239473386000000000000)
      constant := (16304512973239158404645468450599363831457916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree012.table
  base := (4486230615570955753981575063032183403909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-7979235420889328916290309282980330000000000000)
      constant := (29494506453569903892385525026128273246527656282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165493076447915378051/100000000000000000000)
  centralHi := (41373269111978844513/25000000000000000000)
  directionLo := (34570376189940256853/20000000000000000000)
  directionHi := (86425940474850642133/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree013.table
  base := (3376201318089842140071443331869180588729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-23884501182570857172682635042050000000000000)
      constant := (87174956251981184419927891618458039841004722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree013.table
  base := (3336813174385003695270884324242054583559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-8648235148924964541074242619825200000000000000)
      constant := (31564475908153079820812817547032645621209081982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34570376189940256853/20000000000000000000)
  centralHi := (86425940474850642133/50000000000000000000)
  directionLo := (179909941758380456363/100000000000000000000)
  directionHi := (44977485439595114091/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree014.table
  base := (4765419236112551978593878612851092663407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-25732160727093844178959072717170000000000000)
      constant := (94398120155409734162998872947908063693466063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree014.table
  base := (2346562879611193915547449455921847917167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-9317234876960600165858175956670070000000000000)
      constant := (34202385984869716905164357893860613399393813966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179909941758380456363/100000000000000000000)
  centralHi := (44977485439595114091/25000000000000000000)
  directionLo := (186701369944513235327/100000000000000000000)
  directionHi := (1458604452691509651/781250000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree015.table
  base := (3040389105413383714068644336013718600359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-27579820271616831185235510392290000000000000)
      constant := (103064800745329684849772000945354304388193031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree015.table
  base := (2973799738817482142176514914770773478371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-9986234604996235790642109293514940000000000000)
      constant := (37362654719229670282307000077843794789553475579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186701369944513235327/100000000000000000000)
  centralHi := (1458604452691509651/781250000000000000)
  directionLo := (96627138960558244641/50000000000000000000)
  directionHi := (193254277921116489283/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree016.table
  base := (9598570927013360727370800324233739803/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-5885495963227963638302389613482000000000000)
      constant := (22616646836601420841980460437959434599194464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree016.table
  base := (368589059436894314661558273345738775601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-10655234333031871415426042630359810000000000000)
      constant := (41012353807405828976157610366347744163456967396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96627138960558244641/50000000000000000000)
  centralHi := (193254277921116489283/100000000000000000000)
  directionLo := (24949019999060795503/12500000000000000000)
  directionHi := (7983686399699454561/4000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree017.table
  base := (13752027067263680527719306454116285761/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-31275139360662805197788385742530000000000000)
      constant := (124383762896778419673934709007734286003936784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree017.table
  base := (20424477653335559593208929995782723327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-11324234061067507040209975967204680000000000000)
      constant := (45126443801527541080892770785702956745475142584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24949019999060795503/12500000000000000000)
  centralHi := (7983686399699454561/4000000000000000000)
  directionLo := (205734889423550172131/100000000000000000000)
  directionHi := (51433722355887543033/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree018.table
  base := (-116472138079429198711637640256557481537/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-33122798905185792204064823417650000000000000)
      constant := (136911273519980497890590199180146116186278136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree018.table
  base := (-983960668196667456291180137694516054549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-11993233789103142664993909304049550000000000000)
      constant := (49685084842364288297465479353882505866815954499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205734889423550172131/100000000000000000000)
  centralHi := (51433722355887543033/25000000000000000000)
  directionLo := (211699454703536160581/100000000000000000000)
  directionHi := (105849727351768080291/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree019.table
  base := (-1940015368844193253613426931216906958559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-34970458449708779210341261092770000000000000)
      constant := (150620795000808034719766091587161852528543169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree019.table
  base := (-397606996240046998741682335818602281933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-7015087821129517058048666283044000000000000)
      constant := (30289236216155038459829744993341957559210003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211699454703536160581/100000000000000000000)
  centralHi := (105849727351768080291/50000000000000000000)
  directionLo := (217500513832562475557/100000000000000000000)
  directionHi := (108750256916281237779/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree020.table
  base := (-1410828438091566426364470108107465455761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-36818117994231766216617698767890000000000000)
      constant := (165474830632018572458012445261181217616447902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree020.table
  base := (-1432891134811358426808581483186558087161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-13331233245174413914561775977739290000000000000)
      constant := (60073882516035590994415391554871274879903095422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217500513832562475557/100000000000000000000)
  centralHi := (108750256916281237779/50000000000000000000)
  directionLo := (1785206550076853697/800000000000000000)
  directionHi := (111575409379803356063/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree021.table
  base := (-1795531173710652633787653114705331491953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-38665777538754753222894136443010000000000000)
      constant := (181441657581433273292225975659731845468551646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree021.table
  base := (-453943944760069200961928887914752782911/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-14000232973210049539345709314584160000000000000)
      constant := (65879075664660172103289537767134827714163247688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1785206550076853697/800000000000000000)
  centralHi := (111575409379803356063/50000000000000000000)
  directionLo := (228661545321326351481/100000000000000000000)
  directionHi := (114330772660663175741/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree022.table
  base := (-4260498000369221574509769201212193555803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-40513437083277740229170574118130000000000000)
      constant := (198494179773908718254733530277842264435231173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree022.table
  base := (-4297600149452316146201355437525706823557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-14669232701245685164129642651429030000000000000)
      constant := (72077876242110374268749665385170232619261293907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228661545321326351481/100000000000000000000)
  centralHi := (114330772660663175741/50000000000000000000)
  directionLo := (117021276595744680851/50000000000000000000)
  directionHi := (234042553191489361703/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree023.table
  base := (-2420253271831525775258596075866196122657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-42361096627800727235447011793250000000000000)
      constant := (216609108366067608308175546704083145530101374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree023.table
  base := (-2437231117933617441788192806308008391649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-15338232429281320788913575988273900000000000000)
      constant := (78661883767406934826029854832122486282175793198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117021276595744680851/50000000000000000000)
  centralHi := (234042553191489361703/100000000000000000000)
  directionLo := (29912824146813809891/12500000000000000000)
  directionHi := (239302593174510479129/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree024.table
  base := (-5340186337026720235707093514230279359131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-44208756172323714241723449468370000000000000)
      constant := (235766345081279793038950098719385312895679621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree024.table
  base := (-214849081910741155910135783659792644937/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-3201446431463391282739501865023754000000000000)
      constant := (17124770008564427832930322899319054075438171435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29912824146813809891/12500000000000000000)
  centralHi := (239302593174510479129/100000000000000000000)
  directionLo := (122224737160383588507/50000000000000000000)
  directionHi := (48889894864153435403/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree025.table
  base := (-288370527549533203027074248866815476363/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-9211283143369340249599977428698000000000000)
      constant := (51189699617168707674433320500712818450856532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree025.table
  base := (-5795757721502035584542234334933571643721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-16676231885352592038481442661963640000000000000)
      constant := (92957504618140135599163773742323339476286332271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122224737160383588507/50000000000000000000)
  centralHi := (48889894864153435403/20000000000000000000)
  directionLo := (24949019999060795503/10000000000000000000)
  directionHi := (249490199990607955031/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree026.table
  base := (-6129004799914165004345318943098478268353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-47904075261369688254276324818610000000000000)
      constant := (277140489597639190415496238200495461505208223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree026.table
  base := (-1230973798342962102874694313867152315727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-3469046322677645532653075199761702000000000000)
      constant := (20131482618006272862396409512780593252975819577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24949019999060795503/10000000000000000000)
  centralHi := (249490199990607955031/100000000000000000000)
  directionLo := (50886215928091055409/20000000000000000000)
  directionHi := (127215539820227638523/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree027.table
  base := (-803861799859017906190144372575718878009/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-49751734805892675260552762493730000000000000)
      constant := (299329230595666250486011751722061895987824952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree027.table
  base := (-3227237328841310846442677770581329753559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-18014231341423863288049309335653380000000000000)
      constant := (108718859505177163382778219737992854588708258018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50886215928091055409/20000000000000000000)
  centralHi := (127215539820227638523/50000000000000000000)
  directionLo := (259277821424551926397/100000000000000000000)
  directionHi := (129638910712275963199/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree028.table
  base := (-6678228314368821817840068236429696792133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-51599394350415662266829200168850000000000000)
      constant := (322503347012916889928620838069486799786178203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree028.table
  base := (-53597694298303857224097670493105604783/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-3736646213891899782566648534499650000000000000)
      constant := (23427549462786338135190369534493507714285035825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259277821424551926397/100000000000000000000)
  centralHi := (129638910712275963199/50000000000000000000)
  directionLo := (264035609489167161619/100000000000000000000)
  directionHi := (13201780474458358081/5000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree029.table
  base := (-26857361522766268441972302647305489373/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-53447053894938649273105637843970000000000000)
      constant := (346652946939827572241162639898158156537611008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree029.table
  base := (-6895046346894508843106117074215901582333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-19352230797495134537617176009343120000000000000)
      constant := (125910515135884246219656508983168204749070131483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264035609489167161619/100000000000000000000)
  centralHi := (13201780474458358081/5000000000000000000)
  directionLo := (268709168942874225523/100000000000000000000)
  directionHi := (67177292235718556381/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree030.table
  base := (-7026560332039600579610398611296504857103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-55294713439461636279382075519090000000000000)
      constant := (371769421402420449601671200933846020770659473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree030.table
  base := (-7044363599998964781117548305947407333983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-20021230525530770162401109346187990000000000000)
      constant := (135034064671544599841990620932262995968922590633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268709168942874225523/100000000000000000000)
  centralHi := (67177292235718556381/25000000000000000000)
  directionLo := (34162852602832789947/12500000000000000000)
  directionHi := (273302820822662319577/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree031.table
  base := (-7134849616693219803606911112985996535989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-57142372983984623285658513194210000000000000)
      constant := (397845273152576112293638361750513933652000299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree031.table
  base := (-7151045785130169251984813499267288456883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-20690230253566405787185042683032860000000000000)
      constant := (144505698758180183132999412357145956337347108533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34162852602832789947/12500000000000000000)
  centralHi := (273302820822662319577/100000000000000000000)
  directionLo := (55564105775321681683/20000000000000000000)
  directionHi := (8681891527394012763/3125000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree032.table
  base := (-180082746990462945330229828066298779577/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-11798006505701522058386990173866000000000000)
      constant := (84974793825237440986823801625036367967315256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree032.table
  base := (-7218039039837632324589309781240508811273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-21359229981602041411968976019877730000000000000)
      constant := (154323068001348276837763482000236257488959157423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55564105775321681683/20000000000000000000)
  centralHi := (8681891527394012763/3125000000000000000)
  directionLo := (11290637584188595231/4000000000000000000)
  directionHi := (35283242450589360097/12500000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree033.table
  base := (-5651968578553798467758185166286785863/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-12167538414606119459642277708890000000000000)
      constant := (90569962612780543773910241949376157447330048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree033.table
  base := (-7247911161453218247157557145561379165063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-22028229709637677036752909356722600000000000000)
      constant := (164484124713634383143398839719082364996199675713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11290637584188595231/4000000000000000000)
  centralHi := (35283242450589360097/12500000000000000000)
  directionLo := (35830302088583722181/12500000000000000000)
  directionHi := (286642416708669777449/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree034.table
  base := (-903841126225343460392647069471323442423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-62685351617553584304487826219570000000000000)
      constant := (481767835399809098196573322592822772125500744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree034.table
  base := (-7242901520227339487955932252224395684947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-22697229437673312661536842693567470000000000000)
      constant := (174987083111471680877498931712548327885434699797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35830302088583722181/12500000000000000000)
  centralHi := (286642416708669777449/100000000000000000000)
  directionLo := (1136535433109819079/390625000000000000)
  directionHi := (11638122835044547369/4000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree035.table
  base := (-7193901417145241109797821549406440757777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-64533011162076571310764263894690000000000000)
      constant := (511623697989775311318530772339261172366070607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree035.table
  base := (-3602482114745162488448391443866276265997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-23366229165708948286320776030412340000000000000)
      constant := (185830384889139012565234086150635119965913916694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1136535433109819079/390625000000000000)
  centralHi := (11638122835044547369/4000000000000000000)
  directionLo := (147600392824591573901/50000000000000000000)
  directionHi := (295200785649183147803/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree036.table
  base := (-7125752354579236905958039521895644775427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-66380670706599558317040701569810000000000000)
      constant := (542413611621226964092171459776532520691081757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree036.table
  base := (-285432220383724673582589107588448372253/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-4807045778748916782220941873451442000000000000)
      constant := (39402533884584747951899794897077407169976087015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147600392824591573901/50000000000000000000)
  centralHi := (295200785649183147803/100000000000000000000)
  directionLo := (74847059997182386509/25000000000000000000)
  directionHi := (299388239988729546037/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree037.table
  base := (-3513890514069838092630275252774534833167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-68228330251122545323317139244930000000000000)
      constant := (574134264548032871597467452353262105107068194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree037.table
  base := (-7036916045093400760045591744690313559631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-24704228621780219535888642704102080000000000000)
      constant := (208532747967916020569205039587375855392185818681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74847059997182386509/25000000000000000000)
  centralHi := (299388239988729546037/100000000000000000000)
  directionLo := (2428143424287166897/800000000000000000)
  directionHi := (151758964017947931063/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree038.table
  base := (-6901298540064495343471911440754434146541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-70075989795645532329593576920050000000000000)
      constant := (606782760545349432336170425788133454970290931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree038.table
  base := (-3454799510142900084114042906424241553231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-70285951107523144489397717564950000000000000)
      constant := (610497455127709949680916783793927700817825442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2428143424287166897/800000000000000000)
  centralHi := (151758964017947931063/50000000000000000000)
  directionLo := (307592176485126814967/100000000000000000000)
  directionHi := (38449022060640851871/12500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree039.table
  base := (-674745220689843064385471021370978731903/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-14384729868033703867174002919034000000000000)
      constant := (128071313038185864780546664688107015962452546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree039.table
  base := (-211093575678664458348959255794355478761/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-26042228077851490785456509377791820000000000000)
      constant := (232582260341353676737208535533625180820160617952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307592176485126814967/100000000000000000000)
  centralHi := (38449022060640851871/12500000000000000000)
  directionLo := (311613159912272549203/100000000000000000000)
  directionHi := (77903289978068137301/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree040.table
  base := (-6567246657653333653306368786837981848253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-73771308884691506342146452270290000000000000)
      constant := (674853459259285366185879740195474898097209123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree040.table
  base := (-3287050057160966740175942181683123607339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-26711227805887126410240442714636690000000000000)
      constant := (245109989342273306102070524305946049524902243578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311613159912272549203/100000000000000000000)
  centralHi := (77903289978068137301/25000000000000000000)
  directionLo := (315582914344496295689/100000000000000000000)
  directionHi := (31558291434449629569/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree041.table
  base := (-318078107328256493279953847487913912939/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-15123793685842898669684577989082000000000000)
      constant := (142054299653762079953973381761536792665270996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree041.table
  base := (-1591947531932403502073144340906633382287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-27380227533922762035024376051481560000000000000)
      constant := (257972071309807924432362481925840765713714456548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315582914344496295689/100000000000000000000)
  centralHi := (31558291434449629569/10000000000000000000)
  directionLo := (63900669862473218983/20000000000000000000)
  directionHi := (79875837328091523729/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree042.table
  base := (-47899769182202706901056039773384811359/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-77466627973737480354699327620530000000000000)
      constant := (746608977353755351664146263776915897818620032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree042.table
  base := (-1534207632304219072427414493042826602047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-28049227261958397659808309388326430000000000000)
      constant := (271167895344373896632378479136519483876096887588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63900669862473218983/20000000000000000000)
  centralHi := (79875837328091523729/25000000000000000000)
  directionLo := (323376258586609864503/100000000000000000000)
  directionHi := (40422032323326233063/12500000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree043.table
  base := (-5876748708362232220269564099807443505253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-79314287518260467360975765295650000000000000)
      constant := (783864400746235688660033215784785357296896123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree043.table
  base := (-5881893208145741714211269578662054870203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-28718226989994033284592242725171300000000000000)
      constant := (284696925648471368106996891600040039255811487853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323376258586609864503/100000000000000000000)
  centralHi := (40422032323326233063/12500000000000000000)
  directionLo := (327203329770844649129/100000000000000000000)
  directionHi := (32720332977084464913/10000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree044.table
  base := (-5598891380711986554234627803162582923501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-81161947062783454367252202970770000000000000)
      constant := (822036455250918977910996042211533854321986291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree044.table
  base := (-2801783926159545889406099102338322011589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-29387226718029668909376176062016170000000000000)
      constant := (298558691976151618809304775218281184900360727078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327203329770844649129/100000000000000000000)
  centralHi := (32720332977084464913/10000000000000000000)
  directionLo := (165493076447915378051/50000000000000000000)
  directionHi := (330986152895830756103/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree045.table
  base := (-331132546238356437465970986079837471589/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-83009606607306441373528640645890000000000000)
      constant := (861123987179024751244111339045294224404158384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree045.table
  base := (-5302372358432926117586192352126132260699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-30056226446065304534160109398861040000000000000)
      constant := (312752781331212320527109653322142449204837843149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165493076447915378051/50000000000000000000)
  centralHi := (330986152895830756103/100000000000000000000)
  directionLo := (83681557034852517047/25000000000000000000)
  directionHi := (334726228139410068189/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree046.table
  base := (-198995837201095696379670007511919300921/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-16971453230365885675961015664202000000000000)
      constant := (180225196456132348936773250872430851321327555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree046.table
  base := (-1244690471461468615719292802348305918583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-30725226174100940158944042735705910000000000000)
      constant := (327278830747278093338983599898767233174127620932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83681557034852517047/25000000000000000000)
  centralHi := (334726228139410068189/100000000000000000000)
  directionLo := (338424972778443964973/100000000000000000000)
  directionHi := (169212486389221982487/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree047.table
  base := (-36168913126708912404209428510017564031/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (110)
      previous := (55)
      next := (55)
      square := (893452390968562382145279340000000000000)
      linear := (-39250758576891088902707793570000000000000)
      constant := (426456110582601022113517451130717751804032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree047.table
  base := (-2316568367235556874896989143987654073643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (39710)
      previous := (19855)
      next := (19855)
      square := (322536313139651019954445841740000000000000)
      linear := (-14211962834828689807029414247420000000000000)
      constant := (154882988232495914083839295065077163758829754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338424972778443964973/100000000000000000000)
  centralHi := (169212486389221982487/50000000000000000000)
  directionLo := (171041863732058796263/50000000000000000000)
  directionHi := (342083727464117592527/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree048.table
  base := (-4262651190461913661592096845815871023787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-88552585240875402392357953671250000000000000)
      constant := (983869899647372659088776305697352740908454517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree048.table
  base := (-4265849203089330150940746903967647296081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-32063225630172211408511909409395650000000000000)
      constant := (357325571165818103736104868513320263631387502631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171041863732058796263/50000000000000000000)
  centralHi := (342083727464117592527/100000000000000000000)
  directionLo := (34570376189940256853/10000000000000000000)
  directionHi := (345703761899402568531/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree049.table
  base := (-242143758302250925351229128039451453739/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-90400244785398389398634391346370000000000000)
      constant := (1026610344373860008165894209481393627819048784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree049.table
  base := (-3877209563239285317736230814416828638307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-32732225358207847033295842746240520000000000000)
      constant := (372845733802253667973532963277658615669210721157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34570376189940256853/10000000000000000000)
  centralHi := (345703761899402568531/100000000000000000000)
  directionLo := (174643139993425568521/50000000000000000000)
  directionHi := (349286279986851137043/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree050.table
  base := (-3464843883122408242083247613329289725281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-92247904329921376404910829021490000000000000)
      constant := (1070262272384126671954937592359155598996854271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree050.table
  base := (-1733745632798933391389654945971302185789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-33401225086243482658079776083085390000000000000)
      constant := (388696790851921333637501842936229762086489495478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174643139993425568521/50000000000000000000)
  centralHi := (349286279986851137043/100000000000000000000)
  directionLo := (352832424505893600969/100000000000000000000)
  directionHi := (35283242450589360097/10000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree051.table
  base := (-189657880282355120140104728799528646283/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-94095563874444363411187266696610000000000000)
      constant := (1114825145470351387671575689757609459525773648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree051.table
  base := (-75923387000324238658452165171312731581/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-6814044962855823656572741883986052000000000000)
      constant := (80975709998833413341588541888437885918107705048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352832424505893600969/100000000000000000000)
  centralHi := (35283242450589360097/10000000000000000000)
  directionLo := (89085820342788436881/25000000000000000000)
  directionHi := (14253731254846149901/4000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree052.table
  base := (-103342473236886901907525121708131018957/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-19188644683793470083492740874346000000000000)
      constant := (232059697698021662308397834360477692895619935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree052.table
  base := (-323219382094390732528685698695841301281/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-34739224542314753907647642756775130000000000000)
      constant := (421390841491755481511176408065933670401078142648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89085820342788436881/25000000000000000000)
  centralHi := (14253731254846149901/4000000000000000000)
  directionLo := (359819883516760912727/100000000000000000000)
  directionHi := (44977485439595114091/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree053.table
  base := (-33002205400820014428877260571548158903/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-97790882963490337423740142046850000000000000)
      constant := (1206681881681891072387876620815696807486929472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree053.table
  base := (-211413798481059335742477644876152310129/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-7081644854070077906486315218724000000000000000)
      constant := (87646703086611495176809526565858642682879878158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359819883516760912727/100000000000000000000)
  centralHi := (44977485439595114091/12500000000000000000)
  directionLo := (181631607223019924009/50000000000000000000)
  directionHi := (363263214446039848019/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree054.table
  base := (-1620432021304940818544012665441080352897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-99638542508013324430016579721970000000000000)
      constant := (1253974953950054368913467804586960653500450527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree054.table
  base := (-1622250412894084698708263134806298682479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-36077223998386025157215509430464870000000000000)
      constant := (455406439322946650929926601331349921921955803929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181631607223019924009/50000000000000000000)
  centralHi := (363263214446039848019/100000000000000000000)
  directionLo := (183337105740575382761/50000000000000000000)
  directionHi := (366674211481150765523/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree055.table
  base := (-1108583077747330793427196423893074919079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-101486202052536311436293017397090000000000000)
      constant := (1302177376993310278278725438224320197503754489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree055.table
  base := (-44409571603737848709668106131537628823/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-7349244745284332156399888553461948000000000000)
      constant := (94581899195403970535576215821951028497163637365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183337105740575382761/50000000000000000000)
  centralHi := (366674211481150765523/100000000000000000000)
  directionLo := (370053768743108219701/100000000000000000000)
  directionHi := (185026884371554109851/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree056.table
  base := (-576725887650208191695782264045226557899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-103333861597059298442569455072210000000000000)
      constant := (1351288860167629539311641349064324094533601109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree056.table
  base := (-115646935096374764381613941118991180279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-7483044690891459281356675220830922000000000000)
      constant := (98148516335959844024952884074372501602277691729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370053768743108219701/100000000000000000000)
  centralHi := (185026884371554109851/50000000000000000000)
  directionLo := (74680547977805294131/20000000000000000000)
  directionHi := (1458604452691509651/390625000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree057.table
  base := (-6244253106263983415128537705985788753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-105181521141582285448845892747330000000000000)
      constant := (1401309145988854186241249103688449909570578492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree057.table
  base := (-1054070379298416660151655836391661623/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-21099292621879740737710420742936000000000000)
      constant := (281942163198225511499357836354497304097373965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74680547977805294131/20000000000000000000)
  centralHi := (1458604452691509651/390625000000000000)
  directionLo := (94180485157583900579/25000000000000000000)
  directionHi := (376721940630335602317/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree058.table
  base := (136640053556426297965462993926786283041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-107029180686105272455122330422450000000000000)
      constant := (1452238006192835571545052488225097083596950276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree058.table
  base := (27265368294781649026753120484642941963/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-7750644582105713531270248555568870000000000000)
      constant := (105479696648568544725603680175027904117701809548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94180485157583900579/25000000000000000000)
  centralHi := (376721940630335602317/100000000000000000000)
  directionLo := (47501518881626999187/12500000000000000000)
  directionHi := (380012151053015993497/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree059.table
  base := (1137794122842283176572875865240239748751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-108876840230628259461398768097570000000000000)
      constant := (1504075238281737014676720248161335689604990959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree059.table
  base := (227330431146297070691660107447973919483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-7884444527712840656227035222937844000000000000)
      constant := (109244229096995920539341592987236894604117798867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47501518881626999187/12500000000000000000)
  centralHi := (380012151053015993497/100000000000000000000)
  directionLo := (383274117758549392241/100000000000000000000)
  directionHi := (191637058879274696121/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree060.table
  base := (1748643336762783495773870707450284279427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-110724499775151246467675205772690000000000000)
      constant := (1556820662494512390631192984333157677973254243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree060.table
  base := (873801125900518878966520854858405541177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-40091222366599838905919109451534090000000000000)
      constant := (565373527217622267881310274961528611280812114946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383274117758549392241/100000000000000000000)
  centralHi := (191637058879274696121/50000000000000000000)
  directionLo := (96627138960558244641/25000000000000000000)
  directionHi := (77301711168446595713/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree061.table
  base := (297379446039087293517869100621816983537/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-112572159319674233473951643447810000000000000)
      constant := (1610474119147688711675350655653088749733065864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree061.table
  base := (2378086288815963311259027674440821737453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-40760222094635474530703042788378960000000000000)
      constant := (584855571530592908197542892707828240103710157397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96627138960558244641/25000000000000000000)
  centralHi := (77301711168446595713/20000000000000000000)
  directionLo := (389716150723706433987/100000000000000000000)
  directionHi := (97429037680926608497/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree062.table
  base := (11831666255564353223680641618277550033/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-114419818864197220480228081122930000000000000)
      constant := (1665035466299612752550898169832222427653861632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree062.table
  base := (1514020423084403011714736152728299802029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-41429221822671110155486976125223830000000000000)
      constant := (604667227849191528473630896585726429897656448042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389716150723706433987/100000000000000000000)
  centralHi := (97429037680926608497/25000000000000000000)
  directionLo := (392897559842965699523/100000000000000000000)
  directionHi := (98224389960741424881/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree063.table
  base := (924549790560481086231262889689164342617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-116267478408720207486504518798050000000000000)
      constant := (1720504577697416195330540940936553456131363812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree063.table
  base := (3697409526815416734706330166764327984401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-42098221550706745780270909462068700000000000000)
      constant := (624808451199651669006290342000330562836832593049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392897559842965699523/100000000000000000000)
  centralHi := (98224389960741424881/25000000000000000000)
  directionLo := (396053414233750742429/100000000000000000000)
  directionHi := (39605341423375074243/10000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree064.table
  base := (2193431250828103926273757923648724305919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-118115137953243194492780956473170000000000000)
      constant := (1776881340971237611891903224719800063983550142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree064.table
  base := (438614214731336967920313672679140070261/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-8553444255748476281010968559782714000000000000)
      constant := (129055840312647470162188166739480519139779128378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396053414233750742429/100000000000000000000)
  centralHi := (39605341423375074243/10000000000000000000)
  directionLo := (24949019999060795503/6250000000000000000)
  directionHi := (399184319984972728049/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree065.table
  base := (2547425637897367668302045775497985491857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-119962797497766181499057394148290000000000000)
      constant := (1834165656044822451783125091020250099903024226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree065.table
  base := (79596781642267881627961559760931925587/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-43436221006778017029838776135758440000000000000)
      constant := (666079443307887761776021985076634287050155364032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24949019999060795503/6250000000000000000)
  centralHi := (399184319984972728049/100000000000000000000)
  directionLo := (402290859599766745029/100000000000000000000)
  directionHi := (40229085959976674503/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree066.table
  base := (116442502245689249741140325772690057389/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-24362091408457833701066766364682000000000000)
      constant := (378471486747119732024666624547558723367723010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree066.table
  base := (5821525350930371721360545452402446007053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-44105220734813652654622709472603310000000000000)
      constant := (687209144687748029704842226971270978165878407797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402290859599766745029/100000000000000000000)
  centralHi := (40229085959976674503/10000000000000000000)
  directionLo := (405373593260801068697/100000000000000000000)
  directionHi := (202686796630400534349/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree067.table
  base := (6568648011673624465070082560085970694167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-123658116586812155511610269498530000000000000)
      constant := (1951456594520777288383538137504649909263414903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree067.table
  base := (262724025432377932494313016473714947047/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-8954844092569857655881328561889636000000000000)
      constant := (141733655480433371791725393783620072804038415515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405373593260801068697/100000000000000000000)
  centralHi := (202686796630400534349/50000000000000000000)
  directionLo := (408433060009626943233/100000000000000000000)
  directionHi := (204216530004813471617/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree068.table
  base := (7334387854752929604160973121638049129999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-125505776131335142517886707173650000000000000)
      constant := (2011463067449025011272480696529458450528167791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree068.table
  base := (3666944111696666132402682521171875400747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-45443220190884923904190576146293050000000000000)
      constant := (730456816206820362397444890401980091732900588806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408433060009626943233/100000000000000000000)
  centralHi := (204216530004813471617/50000000000000000000)
  directionLo := (205734889423550172131/50000000000000000000)
  directionHi := (411469778847100344263/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree069.table
  base := (4059657983848087652364455525066217901061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-127353435675858129524163144848770000000000000)
      constant := (2072376789179859747247642683588962550686887498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree069.table
  base := (8118859859648971859382488093441978265161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-46112219918920559528974509483137920000000000000)
      constant := (752574738570558136960775437467654613375574374289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205734889423550172131/50000000000000000000)
  centralHi := (411469778847100344263/100000000000000000000)
  directionLo := (414484249761237378743/100000000000000000000)
  directionHi := (51810531220154672343/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree070.table
  base := (8923406737964989647857827736012006135567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-129201095220381116530439582523890000000000000)
      constant := (2134197703135184232740138503124650521553467503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree070.table
  base := (8922990312870462954801833279883199143183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-46781219646956195153758442819982790000000000000)
      constant := (775022024372381541097053145145559127273532140167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414484249761237378743/100000000000000000000)
  centralHi := (51810531220154672343/12500000000000000000)
  directionLo := (104369238672066933343/25000000000000000000)
  directionHi := (417476954688267733373/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree071.table
  base := (4873318637406766205601753525565319278311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-131048754764904103536716020199010000000000000)
      constant := (2196925758749340906698809781709447580571577998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree071.table
  base := (1949251407578657539118032405034024158697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-9490043874998366155708475231365532000000000000)
      constant := (159559731126734335041389746961220888781328763953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104369238672066933343/25000000000000000000)
  centralHi := (417476954688267733373/100000000000000000000)
  directionLo := (420448358412117114487/100000000000000000000)
  directionHi := (52556044801514639311/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree072.table
  base := (661811694312769230468427987071355371823/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-132896414309427090542992457874130000000000000)
      constant := (2260560910805784140664494656787369984261712112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree072.table
  base := (10588639879160674269444180875219042420879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-48119219103027466403326309493672530000000000000)
      constant := (820904616281399947165512757387624970159487537671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420448358412117114487/100000000000000000000)
  centralHi := (52556044801514639311/12500000000000000000)
  directionLo := (423398909407072321163/100000000000000000000)
  directionHi := (105849727351768080291/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree073.table
  base := (11450437927021136999908056885242444544247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-134744073853950077549268895549250000000000000)
      constant := (2325103118849956696381889369451760559998241623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree073.table
  base := (5725060403981314305344400009191012313673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-48788218831063102028110242830517400000000000000)
      constant := (844339891938589600915066678194911868407052440354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423398909407072321163/100000000000000000000)
  centralHi := (105849727351768080291/25000000000000000000)
  directionLo := (85265808125590969887/20000000000000000000)
  directionHi := (106582260156988712359/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree074.table
  base := (12330973335653127115883272247680963019717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-136591733398473064555545333224370000000000000)
      constant := (2390552346669255710700269184368447247310554853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree074.table
  base := (1541335461219104299520724599697437875069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-49457218559098737652894176167362270000000000000)
      constant := (868104469738762811050024295728299697088287191848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85265808125590969887/20000000000000000000)
  centralHi := (106582260156988712359/25000000000000000000)
  directionLo := (42923917025174498721/10000000000000000000)
  directionHi := (429239170251744987211/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree075.table
  base := (6615289326667828042499314298117828205723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-138439392942996051561821770899490000000000000)
      constant := (2456908561832104933731152201124584565012884214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree075.table
  base := (6615157038978953863458612912526944387541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-50126218287134373277678109504207140000000000000)
      constant := (892198338161514079153545495396266554799800365818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42923917025174498721/10000000000000000000)
  centralHi := (429239170251744987211/100000000000000000000)
  directionLo := (216064851187126605331/50000000000000000000)
  directionHi := (432129702374253210663/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree076.table
  base := (14149240725080959867100025074450670388873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-140287052487519038568098208574610000000000000)
      constant := (2524171735279136394709838010928261530889020457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree076.table
  base := (110539054930760818028215524340417954777/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-140706975111274262887706489864410000000000000)
      constant := (2539117692206938085132304897138751857549106304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216064851187126605331/50000000000000000000)
  centralHi := (432129702374253210663/100000000000000000000)
  directionLo := (217500513832562475557/50000000000000000000)
  directionHi := (87000205533024990223/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree077.table
  base := (301738955164409144572522890280101232437/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-28426942406408405114874929249946000000000000)
      constant := (518468368192069039538277932830931436224533330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree077.table
  base := (7543363475369965052768761231735151558089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-51464217743205644527245976177896880000000000000)
      constant := (941373906665081356057683573251016530999693029922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217500513832562475557/50000000000000000000)
  centralHi := (87000205533024990223/20000000000000000000)
  directionLo := (437853523984184630227/100000000000000000000)
  directionHi := (109463380996046157557/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree078.table
  base := (2005461147065121630545753756337009821639/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-143982371576565012580651083924850000000000000)
      constant := (2661418855512832258824216157090747637568004408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree078.table
  base := (4010871859259760508636966296426289073529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-52133217471241280152029909514741750000000000000)
      constant := (966455589203392701925703839623825001181586510084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437853523984184630227/100000000000000000000)
  centralHi := (109463380996046157557/25000000000000000000)
  directionLo := (110171889240467974107/25000000000000000000)
  directionHi := (440687556961871896429/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree079.table
  base := (17019455490533981352650450941738932123069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-145830031121087999586927521599970000000000000)
      constant := (2731402757974405784258990159025721301059859421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree079.table
  base := (8509635580563224944832952694192913574963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-52802217199276915776813842851586620000000000000)
      constant := (991866527062310114851154794657340365724881338774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110171889240467974107/25000000000000000000)
  centralHi := (440687556961871896429/100000000000000000000)
  directionLo := (443503480546294280731/100000000000000000000)
  directionHi := (110875870136573570183/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree080.table
  base := (18014238182296497619369226690199178116361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-147677690665610986593203959275090000000000000)
      constant := (2802293529528885541159862281241849984459041449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree080.table
  base := (18014069751099055441603280396295574533363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-53471216927312551401597776188431490000000000000)
      constant := (1017606713565667841054188662824573709616055790987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443503480546294280731/100000000000000000000)
  centralHi := (110875870136573570183/25000000000000000000)
  directionLo := (446301637519213424251/100000000000000000000)
  directionHi := (111575409379803356063/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree081.table
  base := (19028029602729166365136853024149796359903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-149525350210133973599480396950210000000000000)
      constant := (2874091153279455233272869944802446900159025727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree081.table
  base := (190278756908004984992593117506644556287/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-10828043331069637405276341905055272000000000000)
      constant := (208735228543942901451354479837851480145330237260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446301637519213424251/100000000000000000000)
  centralHi := (111575409379803356063/25000000000000000000)
  directionLo := (224541179991547159527/50000000000000000000)
  directionHi := (89816471996618863811/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree082.table
  base := (20060822880275631819910896756846340037029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-151373009754656960605756834625330000000000000)
      constant := (2946795614046846870701989414797993565141797061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree082.table
  base := (20060682229675442036770786700708296768471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-54809216383383822651165642862121230000000000000)
      constant := (1070074809141226510502968410606491350549720430479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224541179991547159527/50000000000000000000)
  centralHi := (89816471996618863811/20000000000000000000)
  directionLo := (451845969821176623441/100000000000000000000)
  directionHi := (225922984910588311721/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree083.table
  base := (10556305919750551745012723804108766817621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-153220669299179947612033272300450000000000000)
      constant := (3020406898189525001246712695419812531800249578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree083.table
  base := (2639060412808389055110531789208842342129/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-55478216111419458275949576198966100000000000000)
      constant := (1096802707993470901931661345883399933185107431368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451845969821176623441/100000000000000000000)
  centralHi := (225922984910588311721/50000000000000000000)
  directionLo := (454592779132372271009/100000000000000000000)
  directionHi := (45459277913237227101/10000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree084.table
  base := (11091695464260155138353894432926783773687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-155068328843702934618309709975570000000000000)
      constant := (3094924993443375061049850855450190530712149166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree084.table
  base := (11091636728819830663091935589769521299273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-56147215839455093900733509535810970000000000000)
      constant := (1123859834929125870783749726108511899981167909154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454592779132372271009/100000000000000000000)
  centralHi := (45459277913237227101/10000000000000000000)
  directionLo := (228661545321326351481/50000000000000000000)
  directionHi := (457323090642652702963/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree085.table
  base := (727286098570579149732145582430251942889/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-156915988388225921624586147650690000000000000)
      constant := (3170349888778694994982142755369729649338937632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree085.table
  base := (11636523896769640745775489550750057687099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-56816215567490729525517442872655840000000000000)
      constant := (1151246186039372490160508678421436846755038820902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228661545321326351481/50000000000000000000)
  centralHi := (457323090642652702963/100000000000000000000)
  directionLo := (11500929952361517687/2500000000000000000)
  directionHi := (460037198094460707481/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree086.table
  base := (24381900024666508503658688736169518831327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-158763647932748908630862585325810000000000000)
      constant := (3246681574272547982113649020851598467098401343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree086.table
  base := (12190900950712047530229562059759004244093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-57485215295526365150301376209500710000000000000)
      constant := (1178961757808463958291180058638198066350895437514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11500929952361517687/2500000000000000000)
  centralHi := (460037198094460707481/100000000000000000000)
  directionLo := (231367693307782398641/50000000000000000000)
  directionHi := (462735386615564797283/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree087.table
  base := (25509621497112799555378041752653701322913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-160611307477271895637139023000930000000000000)
      constant := (3323920040994761176216003831060632026222314817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree087.table
  base := (12754765907297353940698537538947987163901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-58154215023562000775085309546345580000000000000)
      constant := (1207006547073159810009035386984916343081731377098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231367693307782398641/50000000000000000000)
  centralHi := (462735386615564797283/100000000000000000000)
  directionLo := (58177241633583397999/12500000000000000000)
  directionHi := (465417933068667183993/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree088.table
  base := (3332039491533438511716325451293962065841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-162458967021794882643415460676050000000000000)
      constant := (3402065280906054832932248030001026897627542152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree088.table
  base := (26656233962946791191863507786061999101259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-58823214751597636399869242883190450000000000000)
      constant := (1235380550986483918446746744987144215121299888291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58177241633583397999/12500000000000000000)
  centralHi := (465417933068667183993/100000000000000000000)
  directionLo := (117021276595744680851/25000000000000000000)
  directionHi := (93617021276595744681/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree089.table
  base := (6955495013217648253123155829943841562279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-164306626566317869649691898351170000000000000)
      constant := (3481117286766961521458733351737003784044297244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree089.table
  base := (13910952566172837502446975456979825044783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-59492214479633272024653176220035320000000000000)
      constant := (1264083766985327805157879301947199510254274317134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117021276595744680851/25000000000000000000)
  centralHi := (93617021276595744681/20000000000000000000)
  directionLo := (470737167868884824233/100000000000000000000)
  directionHi := (235368583934442412117/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree090.table
  base := (14503305453423927579066130921442087173571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-166154286110840856655968336026290000000000000)
      constant := (3561076052056349335865307963833531141132836678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree090.table
  base := (14503271214146039942548248738095236242181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-60161214207668907649437109556880190000000000000)
      constant := (1293116192761475914255959217031483216092181992538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470737167868884824233/100000000000000000000)
  centralHi := (235368583934442412117/50000000000000000000)
  directionLo := (236687185758372221767/50000000000000000000)
  directionHi := (94674874303348888707/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree091.table
  base := (6042041166859821684739084512038563234791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-33600389131072768732448954740282000000000000)
      constant := (728388314179699753008342053371633186185653319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree091.table
  base := (30210143243408960598687562081103169423011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-60830213935704543274221042893725060000000000000)
      constant := (1322477826235678028396351003853008397603210698939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236687185758372221767/50000000000000000000)
  centralHi := (94674874303348888707/20000000000000000000)
  directionLo := (95199392856157845407/20000000000000000000)
  directionHi := (118999241070197306759/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree092.table
  base := (982273826185536912286619597318449942451/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-169849605199886830668521211376530000000000000)
      constant := (3723713837997802446888173555919166589531976288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree092.table
  base := (1964544076770813714022167958653420844741/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-61499213663740178899004976230569930000000000000)
      constant := (1352168665534436735174491764578383158787485851344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95199392856157845407/20000000000000000000)
  centralHi := (118999241070197306759/25000000000000000000)
  directionLo := (29912824146813809891/6250000000000000000)
  directionHi := (478605186349020958257/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree093.table
  base := (4084284819575512804893603215941891970601/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-171697264744409817674797649051650000000000000)
      constant := (3806392848580262423405143287658385114904460872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree093.table
  base := (32674226265641668820927562978953439199467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-62168213391775814523788909567414800000000000000)
      constant := (1382188708969215509578262776453671082386175759683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29912824146813809891/6250000000000000000)
  centralHi := (478605186349020958257/100000000000000000000)
  directionLo := (120299817849985546943/25000000000000000000)
  directionHi := (481199271399942187773/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree094.table
  base := (33934752241532909747706529845852478274219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (110)
      previous := (55)
      next := (55)
      square := (893452390968562382145279340000000000000)
      linear := (-78562663779507833717100084530000000000000)
      constant := (1760968129624740821466849446925852478274219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree094.table
  base := (16967352223243933767783363826649171485803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (39710)
      previous := (19855)
      next := (19855)
      square := (322536313139651019954445841740000000000000)
      linear := (-28445999601544341398176932052630000000000000)
      constant := (639446788147490351927400843759770701812749766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120299817849985546943/25000000000000000000)
  centralHi := (481199271399942187773/100000000000000000000)
  directionLo := (241889723423448356353/50000000000000000000)
  directionHi := (483779446846896712707/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree095.table
  base := (17607090867530331183992501304471915753933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-175392583833455791687350524401890000000000000)
      constant := (3974471083397495164414905377197456923800875994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree095.table
  base := (704282760993040117480484265920335835091/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-35183497422629964417372175202828000000000000)
      constant := (799565873854639286499457329045721468597160190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241889723423448356353/50000000000000000000)
  centralHi := (483779446846896712707/100000000000000000000)
  directionLo := (243172967035371503611/50000000000000000000)
  directionHi := (486345934070743007223/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree096.table
  base := (36512565451531053328984339394995040813067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-177240243377978778693626962077010000000000000)
      constant := (4059870300246875710690109345163544045156065003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree096.table
  base := (36512525522752472531678371004520574728613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-64175212575882721398140709577949410000000000000)
      constant := (1474224049600723520196679592344532327796757708237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243172967035371503611/50000000000000000000)
  centralHi := (486345934070743007223/100000000000000000000)
  directionLo := (488898948641534354029/100000000000000000000)
  directionHi := (48889894864153435403/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree097.table
  base := (18914950980077008475251665026042177144003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-179087902922501765699903399752130000000000000)
      constant := (4146176245728578858358317858931874338622205254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree097.table
  base := (7565973093077043853938160585173231072769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-12968842460783671404584928582958856000000000000)
      constant := (301112179156070840747818472517383348195748566281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488898948641534354029/100000000000000000000)
  centralHi := (48889894864153435403/10000000000000000000)
  directionLo := (245719350264916961087/50000000000000000000)
  directionHi := (19657548021193356887/4000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree098.table
  base := (19583094984807690873130530108522243527017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-180935562467024752706179837427250000000000000)
      constant := (4233388916990091602606336378674211271902361106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree098.table
  base := (3916615661398800720945454770776528226027/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-13102642406390798529541715250327830000000000000)
      constant := (307445387967777903785450509386251915314634010246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245719350264916961087/50000000000000000000)
  centralHi := (19657548021193356887/4000000000000000000)
  directionLo := (493965394308251041357/100000000000000000000)
  directionHi := (246982697154125520679/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree099.table
  base := (40521428314252326221589866490632451609621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-182783222011547739712456275102370000000000000)
      constant := (4321508311456464770752444035941627085605652789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree099.table
  base := (40521397828247468765057976189182485535381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-66182211759989628272492509588484020000000000000)
      constant := (1569222180866987711093142502614722260157704043069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493965394308251041357/100000000000000000000)
  centralHi := (246982697154125520679/50000000000000000000)
  directionLo := (496479229343746134153/100000000000000000000)
  directionHi := (248239614671873067077/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree100.table
  base := (5236951992703813585514438969604874021669/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-184630881556070726718732712777490000000000000)
      constant := (4410534426802870901998186140944857333710934568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree100.table
  base := (4189558807888700155309605066152659679749/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-13370242297605052779455288585065778000000000000)
      constant := (320309323608770636588543653144325294617912320602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496479229343746134153/100000000000000000000)
  centralHi := (248239614671873067077/50000000000000000000)
  directionLo := (24949019999060795503/5000000000000000000)
  directionHi := (498980399981215910061/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree101.table
  base := (21644375950688285237437921978324019002827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-186478541100593713725009150452610000000000000)
      constant := (4500467260929935247065915299785535515954489686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree101.table
  base := (21644363218345565454237571601824140067311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-67520211216060899522060376262173760000000000000)
      constant := (1634200250628483983419775587759879598595074179278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24949019999060795503/5000000000000000000)
  centralHi := (498980399981215910061/100000000000000000000)
  directionLo := (501469095718837250783/100000000000000000000)
  directionHi := (15670909241213664087/3125000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree102.table
  base := (8940167067027105086816937908796465326777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-37665240129023340146257117625546000000000000)
      constant := (918261362388310328305732771020075391906850393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree102.table
  base := (10913284194979883775485884986206178973/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-68189210944096535146844309599018630000000000000)
      constant := (1667183077951802655981984653330638647460080136192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501469095718837250783/100000000000000000000)
  centralHi := (15670909241213664087/3125000000000000000)
  directionLo := (503945501375617499289/100000000000000000000)
  directionHi := (50394550137561749929/10000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree103.table
  base := (46131865467536584132816421347982989194929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-190173860189639687737562025802850000000000000)
      constant := (4683053078124926011537935096468954423131598161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree103.table
  base := (46131844199022345467392805410115782403207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-68858210672132170771628242935863500000000000000)
      constant := (1700495099409578843570405252945894936811655018943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503945501375617499289/100000000000000000000)
  centralHi := (50394550137561749929/10000000000000000000)
  directionLo := (25320489862578520077/5000000000000000000)
  directionHi := (506409797251570401541/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree104.table
  base := (47581841598063427596825849490150987625241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-192021519734162674743838463477970000000000000)
      constant := (4775706057932617808479621399449663531664157369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree104.table
  base := (9516364432294944146638025308967125123727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-13905442080033561279282435254541674000000000000)
      constant := (346827262891212373575767155038991088962790972423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25320489862578520077/5000000000000000000)
  centralHi := (506409797251570401541/100000000000000000000)
  directionLo := (50886215928091055409/10000000000000000000)
  directionHi := (508862159280910554091/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree105.table
  base := (12262690773434006184738973838142463079767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-193869179278685661750114901153090000000000000)
      constant := (4869265749966374143682192777375526803772821212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree105.table
  base := (49050745331771493093210230397266147139957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-70196210128203442021196109609553240000000000000)
      constant := (1768106722598250227065109192712094473020611569693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50886215928091055409/10000000000000000000)
  centralHi := (508862159280910554091/100000000000000000000)
  directionLo := (51130275917863471403/10000000000000000000)
  directionHi := (511302759178634714031/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree106.table
  base := (25269314691260470582906237247489286715503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-195716838823208648756391338828210000000000000)
      constant := (4963732152962573160570641697718007668709092254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree106.table
  base := (50538613151367595149181426053399038297487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-70865209856239077645980042946398110000000000000)
      constant := (1802406323390732715677541143849627009691292710663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51130275917863471403/10000000000000000000)
  centralHi := (511302759178634714031/100000000000000000000)
  directionLo := (256865882290417788491/50000000000000000000)
  directionHi := (513731764580835576983/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree107.table
  base := (52045439947395855724112700926837027215359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-197564498367731635762667776503330000000000000)
      constant := (5059105265779112551717366265324002993118728031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree107.table
  base := (26022712557785245002531826600426123533589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-71534209584274713270763976283242980000000000000)
      constant := (1837035116431042774860921378551504299821474028922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256865882290417788491/50000000000000000000)
  centralHi := (513731764580835576983/100000000000000000000)
  directionLo := (516149339179072484063/100000000000000000000)
  directionHi := (16129666849346015127/3125000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree108.table
  base := (6696399290125226180432980874702777004591/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-199412157912254622768944214178450000000000000)
      constant := (5155385087383596376756768944813507475225132152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree108.table
  base := (13392795192073151919755499710698901676001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-72203209312310348895547909620087850000000000000)
      constant := (1871993101355473828020805627283317123770501285796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516149339179072484063/100000000000000000000)
  centralHi := (16129666849346015127/3125000000000000000)
  directionLo := (103711128569820770559/20000000000000000000)
  directionHi := (129638910712275963199/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree109.table
  base := (13778973020205917228926512503100709747959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-201259817456777609775220651853570000000000000)
      constant := (5252571616842688705990224599493417871332965724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree109.table
  base := (55115879697323209098245477882467480265049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-72872209040345984520331842956932720000000000000)
      constant := (1907280277835308833494319842790638010919883060001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103711128569820770559/20000000000000000000)
  centralHi := (129638910712275963199/25000000000000000000)
  directionLo := (104190166354853564729/20000000000000000000)
  directionHi := (260475415887133911823/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree110.table
  base := (2267181313793819564990850105069460132529/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-40621495400260119356299417905738000000000000)
      constant := (1070132970662503263375447778137972187163782805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree110.table
  base := (56679521530067151846233312270172428254303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-73541208768381620145115776293777590000000000000)
      constant := (1942896645573422167556567896118515382738965673047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104190166354853564729/20000000000000000000)
  centralHi := (260475415887133911823/50000000000000000000)
  directionLo := (130833764640945141811/25000000000000000000)
  directionHi := (104667011712756113449/20000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree111.table
  base := (582621162676329944052129328480494267953/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-40991027309164716757554705440762000000000000)
      constant := (1089932959206002978894568090264248236758163540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree111.table
  base := (2913105296485174608573743189924636616721/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-14842041699283451153979941926124492000000000000)
      constant := (395768440860243261086770276067816437431470178916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130833764640945141811/25000000000000000000)
  centralHi := (104667011712756113449/20000000000000000000)
  directionLo := (657135590457757263/125000000000000000)
  directionHi := (525708472366205810401/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree112.table
  base := (299318210184001678313714383216077752683/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-41360559218069314158809992975786000000000000)
      constant := (1109914288861024819625549323317676630227069880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree112.table
  base := (7482954073965216374760948687332044043551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-74879208224452891394683642967467330000000000000)
      constant := (2015116953775859654148606837444434129523885611192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (657135590457757263/125000000000000000)
  centralHi := (525708472366205810401/100000000000000000000)
  directionLo := (528071218978334323239/100000000000000000000)
  directionHi := (13201780474458358081/2500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree113.table
  base := (1921378433431959173720495942823142204739/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-208650455634869557800326402554050000000000000)
      constant := (5650384797513746601923641169114542276168590432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree113.table
  base := (61484101240797863408592454181441618745101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-75548207952488527019467576304312200000000000000)
      constant := (2051720893777795361303395528301961578676662047349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528071218978334323239/100000000000000000000)
  centralHi := (13201780474458358081/2500000000000000000)
  directionLo := (132605860237424571011/25000000000000000000)
  directionHi := (106084688189939656809/20000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree114.table
  base := (63123519511160239657992516135409338440593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-210498115179392544806602840229170000000000000)
      constant := (5752104855091394924845048000277239228615269937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree114.table
  base := (63123511627976279266319587167813469184037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-211127999115025381286015262163870000000000000)
      constant := (5785745219137102561081274795591519953427537733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132605860237424571011/25000000000000000000)
  centralHi := (106084688189939656809/20000000000000000000)
  directionLo := (532765277682932528231/100000000000000000000)
  directionHi := (66595659710366566029/12500000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree115.table
  base := (64781870729662492384766559529737198160393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-212345774723915531812879277904290000000000000)
      constant := (5854731616527457653093264272762289470736308137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree115.table
  base := (64781863528127038568590263243732989601191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-76886207408559798269035442978001940000000000000)
      constant := (2125916344588425998364244709420955385074480161759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532765277682932528231/100000000000000000000)
  centralHi := (66595659710366566029/12500000000000000000)
  directionLo := (267548432765091312711/50000000000000000000)
  directionHi := (535096865530182625423/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree116.table
  base := (830739541452815724205953920253056478627/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-42838686853687703763831143115882000000000000)
      constant := (1191653016272004724511536032115264028180592688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree116.table
  base := (66459156737651154128103207964223130480279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-77555207136595433893819376314846810000000000000)
      constant := (2163507855055231474011582838934339121178368008271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267548432765091312711/50000000000000000000)
  centralHi := (535096865530182625423/100000000000000000000)
  directionLo := (537418337885748451047/100000000000000000000)
  directionHi := (67177292235718556381/12500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree117.table
  base := (68155397081675168624147177776063243323113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-216041093812961505825432153254530000000000000)
      constant := (6062705249171208864013350770925743704500756617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree117.table
  base := (17038847768102324107609452961501580447189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-78224206864631069518603309651691680000000000000)
      constant := (2201428555362068727310409389136859696554121683444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537418337885748451047/100000000000000000000)
  centralHi := (67177292235718556381/12500000000000000000)
  directionLo := (53972982527514136909/10000000000000000000)
  directionHi := (539729825275141369091/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree118.table
  base := (2794822874194374340995791811341182063349/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-43577750671496898566341718185930000000000000)
      constant := (1233610423916587339327324911966015355889689705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree118.table
  base := (13974113273170365319343340845455384026407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-15778641318533341028677448597707310000000000000)
      constant := (447935689075224583057280495934326172536474235743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53972982527514136909/10000000000000000000)
  centralHi := (539729825275141369091/100000000000000000000)
  directionLo := (4336251643525786141/800000000000000000)
  directionHi := (271015727720361633813/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree119.table
  base := (7160468748092008070321594433970087161337/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-43947282580401495967597005720954000000000000)
      constant := (1254861138450625271489394982065323845078786866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree119.table
  base := (14320936493466058969279646454321308115527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-15912441264140468153634235265076284000000000000)
      constant := (455651504995451916462103790005179128085418890623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4336251643525786141/800000000000000000)
  centralHi := (271015727720361633813/50000000000000000000)
  directionLo := (68040419178010805023/12500000000000000000)
  directionHi := (108864670684817288037/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree120.table
  base := (36678871909868049977049076087340883506131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-221584072446530466844261466279890000000000000)
      constant := (6381465966872250037876529270066672023330086758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree120.table
  base := (18339434810143135425919393774147762338321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-80231206048737976392955109662226290000000000000)
      constant := (2317165794056808631080937721591801735715726972516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68040419178010805023/12500000000000000000)
  centralHi := (108864670684817288037/20000000000000000000)
  directionLo := (546605641645324639153/100000000000000000000)
  directionHi := (273302820822662319577/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree121.table
  base := (37564870372257257592895230935703091644839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-223431731991053453850537903955010000000000000)
      constant := (6489532943160222219413609775220436258886898702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree121.table
  base := (37564868281152666140501167333447742393673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-80900205776773612017739042999071160000000000000)
      constant := (2356403252516465943709815022108469318698184280354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546605641645324639153/100000000000000000000)
  centralHi := (273302820822662319577/50000000000000000000)
  directionLo := (274439219989668750533/50000000000000000000)
  directionHi := (548878439979337501067/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree122.table
  base := (76920678140518298552073377371820835034607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-225279391535576440856814341630130000000000000)
      constant := (6598506620863588807545917558995672224591446863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree122.table
  base := (38460337160505031195699626129237661157221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-81569205504809247642522976335916030000000000000)
      constant := (2395969900267301120806853213379667807304329458458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274439219989668750533/50000000000000000000)
  centralHi := (548878439979337501067/100000000000000000000)
  directionLo := (4409134926634423361/800000000000000000)
  directionHi := (275570932914651460063/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree123.table
  base := (15746111180783260828100337709787334845959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-45425410216019885572618155861050000000000000)
      constant := (1341677399950597360190572230444372222674723431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree123.table
  base := (39365276207899259312014656837971937389903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-82238205232844883267306909672760900000000000000)
      constant := (2435865737228860957475792134374300283249281514894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4409134926634423361/800000000000000000)
  centralHi := (275570932914651460063/50000000000000000000)
  directionLo := (553396034197444790407/100000000000000000000)
  directionHi := (69174504274680598801/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree124.table
  base := (80559373940743815110554932451060713464997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-228974710624622414869367216980370000000000000)
      constant := (6819174079620848140133730852238713116044178373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree124.table
  base := (40279685377698485166907568094425434221921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-82907204960880518892090843009605770000000000000)
      constant := (2476090763328359308487445471311351906189673359058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553396034197444790407/100000000000000000000)
  centralHi := (69174504274680598801/12500000000000000000)
  directionLo := (55564105775321681683/10000000000000000000)
  directionHi := (555641057753216816831/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree125.table
  base := (10300891520745360050012779398971127490733/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-230822370169145401875643654655490000000000000)
      constant := (6930867860279323991192279558631117765016233576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree125.table
  base := (41203564628614017648571650814940599855423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-83576204688916154516874776346450640000000000000)
      constant := (2516644978499944922964974927486715414078214431854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55564105775321681683/10000000000000000000)
  centralHi := (555641057753216816831/100000000000000000000)
  directionLo := (278938523449508390157/50000000000000000000)
  directionHi := (111575409379803356063/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree126.table
  base := (21068457625653188626948145740488883162943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-232670029713668388881920092330610000000000000)
      constant := (7043468341558408067316022881894759771627764348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree126.table
  base := (42136913923290403211826405482009850914909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-84245204416951790141658709683295510000000000000)
      constant := (2557528382684039662760079214580916997204486534282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278938523449508390157/50000000000000000000)
  centralHi := (111575409379803356063/20000000000000000000)
  directionLo := (560104109833539705983/100000000000000000000)
  directionHi := (4375813358074528953/781250000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree127.table
  base := (4307973444052085445868265981167152582517/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (394727266329910860431784412412000000000000)
      linear := (-46903537851638275177639306001146000000000000)
      constant := (1431395104660847940042508206524036960219120212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree127.table
  base := (8615946645586066673533131973621911277823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142496543145097820615874172880732000000000000)
      linear := (-16982840828997485153288528604028076000000000000)
      constant := (519748195165348053631651873304124734303177347054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560104109833539705983/100000000000000000000)
  centralHi := (4375813358074528953/781250000000000000)
  directionLo := (281161176306436399729/50000000000000000000)
  directionHi := (562322352612872799459/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree128.table
  base := (11008005904776542826338774530184249464369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-236365348802714362894472967680850000000000000)
      constant := (7271389405377569271032828470911176056534328968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree128.table
  base := (88064045023911064839412385932815494608517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-85583203873023061391226576356985250000000000000)
      constant := (2640282757879277508407905176888481143360067273133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell030.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281161176306436399729/50000000000000000000)
  centralHi := (562322352612872799459/100000000000000000000)
  directionLo := (564531879209429761551/100000000000000000000)
  directionHi := (35283242450589360097/6250000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree129.table
  base := (44993782758536645886866636549804723724303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1973636331649554302158922062060000000000000)
      linear := (-238213008347237349900749405355970000000000000)
      constant := (7386709987652370317111551683933457269413970654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree129.table
  base := (89987563495400283156482169792235357174173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (712482715725489103079370864403660000000000000)
      linear := (-86252203601058697016010509693830120000000000000)
      constant := (2682153728797527160657030658580462394593187084677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell030.Kernel129
