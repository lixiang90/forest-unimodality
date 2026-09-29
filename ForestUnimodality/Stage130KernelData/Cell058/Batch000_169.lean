import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell058.Parameters
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch000_049
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch050_099
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch100_149
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch150_199
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch000_049
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch050_099
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch100_149
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree000.table
  base := (859375308021873115971089871/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (318376190301634873214275955000000000000)
      linear := (5980201238115496597397280500000000000)
      constant := (429687654010936557985544935500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree000.table
  base := (859375308021873115971089871/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (318376190301634873214275955000000000000)
      linear := (5980201238115496597397280500000000000)
      constant := (429687654010936557985544935500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree001.table
  base := (122273745365764303094122205646525945553353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-7217770895459785276341336806056092000000000000)
      constant := (5756478418484918394945742793880712649765618039906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree001.table
  base := (244062963082692811145641460433577040560427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-7237076431699200660965867464277404500000000000)
      constant := (5745085728232792521422765297517456529453120809827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24996025209852469769/50000000000000000000)
  directionHi := (49992050419704939539/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree002.table
  base := (146235683505484622514808312455217820858593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-14576269088475353279827442493691564500000000000)
      constant := (3448336565739593482150564856103384693226403053193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree002.table
  base := (29144555957828886936199128683193796893389/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-14614880160954184049076503810134189500000000000)
      constant := (3436304422098823659553390282423015773742027595945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/50000000000000000000)
  centralHi := (49992050419704939539/100000000000000000000)
  directionLo := (8837429464298288003/12500000000000000000)
  directionHi := (2827977428575452161/4000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree003.table
  base := (185608656240342418260979154374441006009257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-4874392729220204729625232929183786000000000000)
      constant := (488876482157201041159607124659119305686338176073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree003.table
  base := (184776342890535562006726438151181162136521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-4887263086713148319374920034664661000000000000)
      constant := (486719106887213895634698707025162094645577956969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/12500000000000000000)
  centralHi := (2827977428575452161/4000000000000000000)
  directionLo := (86588771301473971569/100000000000000000000)
  directionHi := (8658877130147397157/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree004.table
  base := (62772596240041312672787084290225164375649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-29293265474506489286799653868962509500000000000)
      constant := (1505810060349763299464642161692328348845811773449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree004.table
  base := (31231458725310422515935969962867188261509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-29370487619464150825297776501847759500000000000)
      constant := (1498673800903767181424920011909152853949340702618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86588771301473971569/100000000000000000000)
  centralHi := (8658877130147397157/10000000000000000000)
  directionLo := (24996025209852469769/25000000000000000000)
  directionHi := (99984100839409879077/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree005.table
  base := (90224001234915805076752921987448409451993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-73303527335044114580571519113195964000000000000)
      constant := (2212819318058675891378429500095494783979599126593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree005.table
  base := (89773252233378550849510629303287193618099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-73496582697438268426816825695409089000000000000)
      constant := (2202685042959777011201298009254350770947022905899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/25000000000000000000)
  centralHi := (99984100839409879077/100000000000000000000)
  directionLo := (111785623073057136791/100000000000000000000)
  directionHi := (13973202884132142099/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree006.table
  base := (34119280529976094103143634960918381430847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-4890029095615291699307985027137050500000000000)
      constant := (96392520896683376388387558763799392325039911583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree006.table
  base := (67906628665475557963570618145490201983861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-9805798906216470578115344265235851000000000000)
      constant := (191992844723644072333695958576706571734979534229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111785623073057136791/100000000000000000000)
  centralHi := (13973202884132142099/12500000000000000000)
  directionLo := (122455014723766723037/100000000000000000000)
  directionHi := (61227507361883361519/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree007.table
  base := (53659880588534899023715256018542126097799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-2096684083818497685602366160484446000000000000)
      constant := (29364001599529937806455417067494002641341871951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree007.table
  base := (53407765308308271486776250763033744568753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-2102199951315473509780803491404821000000000000)
      constant := (29261857849946674040121059366252979795399059497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122455014723766723037/100000000000000000000)
  centralHi := (61227507361883361519/50000000000000000000)
  directionLo := (16533316617592682509/12500000000000000000)
  directionHi := (132266532940741460073/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree008.table
  base := (43364744435220557833166362902520933122557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-117454516493137522601488153239008799000000000000)
      constant := (1250635292552128338831903750928428406947568957957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree008.table
  base := (21582853584451308198019719532202521396809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-58881702536484084377740321885274899500000000000)
      constant := (623581860583464310428457162423638132216510146609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16533316617592682509/12500000000000000000)
  centralHi := (132266532940741460073/100000000000000000000)
  directionLo := (8837429464298288003/6250000000000000000)
  directionHi := (141398871428772608049/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree009.table
  base := (35676846119684177964697979362019150608517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-1631747072582329118622967464373824000000000000)
      constant := (13963158489298454349362108840891437278936967357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree009.table
  base := (17756869402885426628916046777366567804679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-818018595873321824269764916433724500000000000)
      constant := (6967359131435359298091368726874740645183147759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/6250000000000000000)
  centralHi := (141398871428772608049/100000000000000000000)
  directionLo := (74988075629557409307/50000000000000000000)
  directionHi := (29995230251822963723/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree010.table
  base := (29671831426181500374893232457607991739141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-146888509265199794615432575989550689000000000000)
      constant := (1058225624420015074509843051056441130811805579341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree010.table
  base := (29534030690176303784989803537686432122211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-147274619989988102307923189153976939000000000000)
      constant := (1056877860070218994741705503113066210672725816411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74988075629557409307/50000000000000000000)
  centralHi := (29995230251822963723/20000000000000000000)
  directionLo := (158088744228244182147/100000000000000000000)
  directionHi := (39522186057061045537/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree011.table
  base := (4964119723477747128073011165263538110381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (33450732)
      previous := (16725366)
      next := (16725366)
      square := (123836239732104503555171204008710000000000000)
      linear := (-1335582691332487029937229647643154000000000000)
      constant := (8428212599012368104740676936424702901225036305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree011.table
  base := (6175399655201049806809383630043723894973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (16725366)
      previous := (8362683)
      next := (8362683)
      square := (61918119866052251777585602004355000000000000)
      linear := (-669546394415281277207208520023514500000000000)
      constant := (4212011279970402412023283950214971433636488026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158088744228244182147/100000000000000000000)
  centralHi := (39522186057061045537/25000000000000000000)
  directionLo := (165804873742690474133/100000000000000000000)
  directionHi := (82902436871345237067/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree012.table
  base := (5201357406707374379997236175128225682827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-9795694557625670368298722152227365500000000000)
      constant := (56016862911831417667216171035977609064810491606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree012.table
  base := (1035060126783457506960853166074822005667/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-9821435272611557547798096363189115500000000000)
      constant := (56032249768805040539063397076635433751754425630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165804873742690474133/100000000000000000000)
  centralHi := (82902436871345237067/50000000000000000000)
  directionLo := (86588771301473971569/50000000000000000000)
  directionHi := (173177542602947943139/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree013.table
  base := (871227924542340479459295489496644724483/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-95519749211646601318174605057681762000000000000)
      constant := (509473525502843671121598221360900968633735770830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree013.table
  base := (17332520916151187354419956781721952859319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-191541442365518002636587007229117649000000000000)
      constant := (1019985152086388675682145880080793342798019431119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86588771301473971569/50000000000000000000)
  centralHi := (173177542602947943139/100000000000000000000)
  directionLo := (18024890115382720601/10000000000000000000)
  directionHi := (180248901153827206011/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree014.table
  base := (14542108602645212998094752567494967558223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-4199112138965802829455539214094581000000000000)
      constant := (21398914380333741016966846034485509674869037527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree014.table
  base := (14460502563957710654186280548336224938189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-4210143873959754477812413875935331000000000000)
      constant := (21435564215367732581397946698487692690340329061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18024890115382720601/10000000000000000000)
  centralHi := (180248901153827206011/100000000000000000000)
  directionLo := (187053124732864303733/100000000000000000000)
  directionHi := (93526562366432151867/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree015.table
  base := (603070013031314437233492565998231805943/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-12248527288630859702794090714772523000000000000)
      constant := (60823761507462744640892840901431266286992967270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree015.table
  base := (2997234137536517604993229797446611298297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-12280703182363218677168308478474710500000000000)
      constant := (60966051351117013545892875128513672797865769266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187053124732864303733/100000000000000000000)
  centralHi := (93526562366432151867/50000000000000000000)
  directionLo := (96809189359139368223/50000000000000000000)
  directionHi := (193618378718278736447/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree016.table
  base := (991037495285453102841266656881422500129/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-117595243790693305328632922120588179500000000000)
      constant := (578047031556494200911642976557285979194790769645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree016.table
  base := (4923017155961776509039746765726469029819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-117904132370523951482625412652129179500000000000)
      constant := (579717321249255729565592637914738272229975701619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96809189359139368223/50000000000000000000)
  centralHi := (193618378718278736447/100000000000000000000)
  directionLo := (24996025209852469769/12500000000000000000)
  directionHi := (199968201678819758153/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree017.table
  base := (4016682665740343415350402998870743744527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-124953741983708873332119027808223652000000000000)
      constant := (615517948676802382479470513634068711628202013927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree017.table
  base := (1994072721675685770676708122291168954687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-125281936099778934870736048997985964500000000000)
      constant := (617586823576065001972682669594243850733308752174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/12500000000000000000)
  centralHi := (199968201678819758153/100000000000000000000)
  directionLo := (103061252160823582199/50000000000000000000)
  directionHi := (206122504321647164399/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree018.table
  base := (1277247955978987723581231384785057108977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-3266968893252455341619879839403929000000000000)
      constant := (16279193775106929977387350022020529881785535085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree018.table
  base := (6335680467276651647516285898614184729727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-3275549131581084401453004576391179000000000000)
      constant := (16340369310328145250715414724137198561865017767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103061252160823582199/50000000000000000000)
  centralHi := (206122504321647164399/100000000000000000000)
  directionLo := (26512288392894864009/12500000000000000000)
  directionHi := (212098307143158912073/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree019.table
  base := (2466691269617086325283504852131135932343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-139670738369740009339091239183494597000000000000)
      constant := (708996170603411883724357171768001108680717876943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree019.table
  base := (4888664050568753430298789887348326030627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-280075087116577803293914643379399069000000000000)
      constant := (1423787132488124331896409621160947066166246720027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512288392894864009/12500000000000000000)
  centralHi := (212098307143158912073/100000000000000000000)
  directionLo := (27238786969985493351/12500000000000000000)
  directionHi := (217910295759883946809/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree020.table
  base := (1822852267016976344217245329688741418111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-147029236562755577342577344871130069500000000000)
      constant := (764242151826179400421368608539247057988013092311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree020.table
  base := (3606214547628300038382453285217995408269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-294830694575087770070135916071112639000000000000)
      constant := (1535142230915129813433966554639915726764463170069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27238786969985493351/12500000000000000000)
  centralHi := (217910295759883946809/100000000000000000000)
  directionLo := (223571246146114273583/100000000000000000000)
  directionHi := (13973202884132142099/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree021.table
  base := (249925783080369678619516130783792949349/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (4589046)
      previous := (2294523)
      next := (2294523)
      square := (16988871890685538469586979234755000000000000)
      linear := (-350085566339617109628261792650262000000000000)
      constant := (1870212058430647871209021689416012190351059945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree021.table
  base := (492887658407916697503077962774071689883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9178092)
      previous := (4589046)
      next := (4589046)
      square := (33977743781371076939173958469510000000000000)
      linear := (-702009755178226160649336028940649000000000000)
      constant := (3757535008745747891333104695148930197219233815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223571246146114273583/100000000000000000000)
  centralHi := (13973202884132142099/6250000000000000000)
  directionLo := (229092355194346756381/100000000000000000000)
  directionHi := (114546177597173378191/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree022.table
  base := (1474222211892090320749421317994234216467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (33450732)
      previous := (16725366)
      next := (16725366)
      square := (123836239732104503555171204008710000000000000)
      linear := (-2673491453698953939661976136304149000000000000)
      constant := (14716149781087662384417810284886349664652718627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree022.table
  base := (1443564849152052167169043626578847385579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (33450732)
      previous := (16725366)
      next := (16725366)
      square := (123836239732104503555171204008710000000000000)
      linear := (-2680511648695104988616350921111899000000000000)
      constant := (14786066235300043029490708896680493818394789499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229092355194346756381/100000000000000000000)
  centralHi := (114546177597173378191/50000000000000000000)
  directionLo := (58620875288617886087/25000000000000000000)
  directionHi := (234483501154471544349/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree023.table
  base := (138533621869336175934205384273391763539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-169104731141802281353035661934036487000000000000)
      constant := (960739076243849247963263305192305745425188438678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree023.table
  base := (527177643558417683108270525042726573777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-339097516950617670398799734146253349000000000000)
      constant := (1930879139606205005547287717914503562322161693177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58620875288617886087/25000000000000000000)
  centralHi := (234483501154471544349/100000000000000000000)
  directionLo := (47950690263571964097/20000000000000000000)
  directionHi := (119876725658929910243/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree024.table
  base := (-274714738033165933509415317574473566577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-39214050963292855412560392804815991000000000000)
      constant := (230186278912381253175889513640670811284680350447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree024.table
  base := (-74597215075341476126579457309965807843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-19658506911618202065278944824331495500000000000)
      constant := (115669263007333476021616700039471547623713588346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47950690263571964097/20000000000000000000)
  centralHi := (119876725658929910243/50000000000000000000)
  directionLo := (9796401177901337843/4000000000000000000)
  directionHi := (61227507361883361519/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree025.table
  base := (-511881444367419425843122233623608982737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-183821727527833417360007873309307432000000000000)
      constant := (1115490024460035182485210965630684707885327385863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree025.table
  base := (-1044530940068361960021386203620770556067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-368608731867637603951242279529680489000000000000)
      constant := (2242348618552596586150272475901350699499749586533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9796401177901337843/4000000000000000000)
  centralHi := (61227507361883361519/25000000000000000000)
  directionLo := (24996025209852469769/10000000000000000000)
  directionHi := (249960252098524697691/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree026.table
  base := (-53205175016097034686346910091180491079/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-191180225720848985363493978996942904500000000000)
      constant := (1199581951734614957015378746714520284706404241936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree026.table
  base := (-1720765871572707096824021756555071803917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-383364339326147570727463552221394059000000000000)
      constant := (2411560830420179842187119117669808381740792568683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/10000000000000000000)
  centralHi := (249960252098524697691/100000000000000000000)
  directionLo := (254910440614589855517/100000000000000000000)
  directionHi := (127455220307294927759/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree027.table
  base := (-2319115620881646847826662426948971308281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-4902190713922581564616792214434034000000000000)
      constant := (31802962801456998773006194888060039031546895599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree027.table
  base := (-467010179536901379745287487389941325883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-4915061071415525154366479319914909000000000000)
      constant := (31969087880199101172964804748733087280315724785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254910440614589855517/100000000000000000000)
  centralHi := (127455220307294927759/50000000000000000000)
  directionLo := (64941578476105478677/25000000000000000000)
  directionHi := (259766313904421914709/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree028.table
  base := (-2880105063055998528785238148755748872589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-8403968249260413117161885321314851000000000000)
      constant := (56356139165571171799896940777728593359688005339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree028.table
  base := (-2894045503047191417745712742653710535283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-8426031719248316413875634644996351000000000000)
      constant := (56653015711209245618486863401177616169140874533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64941578476105478677/25000000000000000000)
  centralHi := (259766313904421914709/100000000000000000000)
  directionLo := (52906613176296584029/20000000000000000000)
  directionHi := (132266532940741460073/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree029.table
  base := (-3391141983888538268530264232129330056371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-426511440599791378747904592119698644000000000000)
      constant := (2955264430133118942030650305348634578743136297429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree029.table
  base := (-850831988729075828783949213042704026713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-213815580850838735528063685148267384500000000000)
      constant := (1485467258086634107402768819794221517519760629374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52906613176296584029/20000000000000000000)
  centralHi := (132266532940741460073/50000000000000000000)
  directionLo := (67303857639172188009/25000000000000000000)
  directionHi := (269215430556688752037/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree030.table
  base := (-38569297673988675929821593158391451667/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-24512690943656806375270933527498310500000000000)
      constant := (175409452166682334504040911457833058181613171850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree030.table
  base := (-3867574598068009081445301329328136067197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-49154085462243048648038738109805371000000000000)
      constant := (352688479175883853738237628427632850234596743267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67303857639172188009/25000000000000000000)
  centralHi := (269215430556688752037/100000000000000000000)
  directionLo := (54763547421616004967/20000000000000000000)
  directionHi := (68454434277020006209/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree031.table
  base := (-2140708010238285360393715462447489940629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-227972716685926825380924507435120267000000000000)
      constant := (1683837524917840987340795418879619838334140305571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree031.table
  base := (-858141724391151338564380896699862343159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-457142376618697404608569915679961909000000000000)
      constant := (3385690837795532823903908983778940332342257185205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54763547421616004967/20000000000000000000)
  centralHi := (68454434277020006209/25000000000000000000)
  directionLo := (55668791350326960539/20000000000000000000)
  directionHi := (34792994593954350337/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree032.table
  base := (-2333958182913638311176912789665574591679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-235331214878942393384410613122755739500000000000)
      constant := (1793050569369684889047077728418435219928116844521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree032.table
  base := (-935204739508092687984655101408019133511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-471897984077207371384791188371675479000000000000)
      constant := (3605340584483922466756716929753153841691866561445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55668791350326960539/20000000000000000000)
  centralHi := (34792994593954350337/12500000000000000000)
  directionLo := (8837429464298288003/3125000000000000000)
  directionHi := (282797742857545216097/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree033.table
  base := (-1003843500263238863092954571300431582019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (3716748)
      previous := (1858374)
      next := (1858374)
      square := (13759582192456055950574578223190000000000000)
      linear := (-445711135118380094376302513885016000000000000)
      constant := (3500994332944954143064222244435478494720757145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree033.table
  base := (-2513143431961780833517879057093690018699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 108045000000000000000000000000000000000000000
      center := (1858374)
      previous := (929187)
      next := (929187)
      square := (6879791096228027975287289111595000000000000)
      linear := (-223440583808869301267682489009820500000000000)
      constant := (1759908373796057780940732347076596452385933309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/3125000000000000000)
  centralHi := (282797742857545216097/100000000000000000000)
  directionLo := (143591232732441386951/50000000000000000000)
  directionHi := (287182465464882773903/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree034.table
  base := (-5337663095417596501380715276388287392057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-500096422529947058782765648996053369000000000000)
      constant := (4047064967671123877255064853090214103044348872543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree034.table
  base := (-1335956060853760759678441440719885012621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-250704599497113652468616866877551309500000000000)
      constant := (2034427829974728828070942158694324567872230182358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143591232732441386951/50000000000000000000)
  centralHi := (287182465464882773903/100000000000000000000)
  directionLo := (7287531028049507897/2500000000000000000)
  directionHi := (291501241121980315881/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree035.table
  base := (-87894147643328848719870459008212924417/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-5253198152203859130507529187462493000000000000)
      constant := (43770419830990139299506467766470828602873125344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree035.table
  base := (-1407648130567068697580279364503006392763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-5266987820946298690953622514763430500000000000)
      constant := (44006328620557609385777847236426533865763924026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7287531028049507897/2500000000000000000)
  centralHi := (291501241121980315881/100000000000000000000)
  directionLo := (36969619850464133481/12500000000000000000)
  directionHi := (295756958803713067849/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree036.table
  base := (-5883565338208197825178523773342972871811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-6537412534592707787613704589464139000000000000)
      constant := (56047558940357352987638425103527445178308596469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree036.table
  base := (-5888238615599631184975642918092982386881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-6554573011249965907279954063438639000000000000)
      constant := (56349818730689254078160907798229302663980944999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36969619850464133481/12500000000000000000)
  centralHi := (295756958803713067849/100000000000000000000)
  directionLo := (74988075629557409307/25000000000000000000)
  directionHi := (299952302518229637229/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree037.table
  base := (-3057041013712382637754930399910312303621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-272123705844020233401841141560933102000000000000)
      constant := (2399042716041970157077320716028049160710917600179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree037.table
  base := (-382384344533703729762686258492977456389/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-272838010684878602632948775915121664500000000000)
      constant := (2411984179078006896340147176474990408262282542488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74988075629557409307/25000000000000000000)
  centralHi := (299952302518229637229/100000000000000000000)
  directionLo := (152044885552880296803/50000000000000000000)
  directionHi := (304089771105760593607/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree038.table
  base := (-6317955106457515942301307364064229948623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-558964408074071602810654494497137149000000000000)
      constant := (5064172858841634957757419085650756360938783890777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree038.table
  base := (-3160746975958446457984073777536848521831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-280215814414133586021059412260978449500000000000)
      constant := (2545745912364070291655853817032345694177720019969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152044885552880296803/50000000000000000000)
  centralHi := (304089771105760593607/100000000000000000000)
  directionLo := (308171695644360225553/100000000000000000000)
  directionHi := (154085847822180112777/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree039.table
  base := (-1624044877754852261522203808021057822949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-31871189136672374378757039215133783000000000000)
      constant := (296560618967491671562477224971424137746442604278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree039.table
  base := (-6499257294890786970946004606798373764429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-63909692920753015424260010801518941000000000000)
      constant := (596320281020597364183867909024467025900258902419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308171695644360225553/100000000000000000000)
  centralHi := (154085847822180112777/50000000000000000000)
  directionLo := (312200254806889150359/100000000000000000000)
  directionHi := (7805006370172228759/2500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree040.table
  base := (-6649594862271492193751646421751429106701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-588398400846133874824598917247679039000000000000)
      constant := (5619820521669660079600502547024531408223861621099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree040.table
  base := (-831533840906392081011770418373245912797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-294971421872643552797280684952692019500000000000)
      constant := (2825060455948318833841561134518241266630530095212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312200254806889150359/100000000000000000000)
  centralHi := (7805006370172228759/2500000000000000000)
  directionLo := (63235497691297672859/20000000000000000000)
  directionHi := (39522186057061045537/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree041.table
  base := (-6778910064157848681439554036452656545283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-603115397232165010831571128622949984000000000000)
      constant := (5909344317535963071299418062138174408817434842117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree041.table
  base := (-3390617865717192733372794679196705821663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-302349225601898536185391321298548804500000000000)
      constant := (2970595232718116197387275082747005492066756129737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63235497691297672859/20000000000000000000)
  centralHi := (39522186057061045537/12500000000000000000)
  directionLo := (320105309721377714103/100000000000000000000)
  directionHi := (40013163715172214263/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree042.table
  base := (-6884723939859571926599480716378813754737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9178092)
      previous := (4589046)
      next := (4589046)
      square := (33977743781371076939173958469510000000000000)
      linear := (-1400980484395002600540914603170569000000000000)
      constant := (14074032737837410688258952911070568119233478943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree042.table
  base := (-6886744609149573040082627719525470880951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9178092)
      previous := (4589046)
      next := (4589046)
      square := (33977743781371076939173958469510000000000000)
      linear := (-1404657729392986483326539490450819000000000000)
      constant := (14149835037735353050418879085156584348321573689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320105309721377714103/100000000000000000000)
  centralHi := (40013163715172214263/12500000000000000000)
  directionLo := (161992757875919776023/50000000000000000000)
  directionHi := (323985515751839552047/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree043.table
  base := (-6967542557171236924023444444873339908333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-632549390004227282845515551373491874000000000000)
      constant := (6511720972331603640781823341576717340860786269067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree043.table
  base := (-3484648851966466638878424712579527791627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-317104833060408502961612593990262374500000000000)
      constant := (3273384748163574430959356096800875232022347318973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161992757875919776023/50000000000000000000)
  centralHi := (323985515751839552047/100000000000000000000)
  directionLo := (163909898665510585539/50000000000000000000)
  directionHi := (327819797331021171079/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree044.table
  base := (-7027793783826442815782273382585362147201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (33450732)
      previous := (16725366)
      next := (16725366)
      square := (123836239732104503555171204008710000000000000)
      linear := (-5349308978431887759111469113626139000000000000)
      constant := (56401254989275794905897976041397597184250202319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree044.table
  base := (-439332366501360520362121835906666042993/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (16725366)
      previous := (8362683)
      next := (8362683)
      square := (61918119866052251777585602004355000000000000)
      linear := (-2681674684212094928510109341620819500000000000)
      constant := (28352302681587166136481412037620488450341426936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163909898665510585539/50000000000000000000)
  centralHi := (327819797331021171079/100000000000000000000)
  directionLo := (165804873742690474133/50000000000000000000)
  directionHi := (331609747485380948267/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree045.table
  base := (-1766459880905945176379503790385675968081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-4086317177631417005305308482247122000000000000)
      constant := (44105756574726355757098623550313848876654279598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree045.table
  base := (-1766790648919698462407380802201612362377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-4097042475542203330096714403481184500000000000)
      constant := (44342790719647492226661821270845285749739743166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165804873742690474133/50000000000000000000)
  centralHi := (331609747485380948267/100000000000000000000)
  directionLo := (2682854953753371283/800000000000000000)
  directionHi := (41919608652396426297/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree046.table
  base := (-1770496502344436698090902448010601146727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-338350189581160345433216092749652354500000000000)
      constant := (3736727950104677733809528356979334056868779487746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree046.table
  base := (-3541567141116472890763071224407440804777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-339238244248173453125944503027832729500000000000)
      constant := (3756793461749135949758363487058384161586385875823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2682854953753371283/800000000000000000)
  centralHi := (41919608652396426297/12500000000000000000)
  directionLo := (67812516495894991313/20000000000000000000)
  directionHi := (169531291239737478283/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree047.table
  base := (-3538246233285364022330768914483148712819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-345708687774175913436702198437287827000000000000)
      constant := (3904757879433636418211039154088256108939552015381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree047.table
  base := (-442343048871795721357611565153825953403/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-346616047977428436514055139373689514500000000000)
      constant := (3925707854391060390821002966459707685464031759976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67812516495894991313/20000000000000000000)
  centralHi := (169531291239737478283/50000000000000000000)
  directionLo := (137091292177332447/40000000000000000)
  directionHi := (342728230443331117501/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree048.table
  base := (-440598650619851454861370982371041235793/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-39229687329687942382243144902769255500000000000)
      constant := (452961498634168237913393880976031490497805092984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree048.table
  base := (-7050442666188841009991679327677845374831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-78665300379262982200481283493232511000000000000)
      constant := (910779261781511413882612823801750710154728507441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137091292177332447/40000000000000000)
  centralHi := (342728230443331117501/100000000000000000000)
  directionLo := (346355085205895886277/100000000000000000000)
  directionHi := (173177542602947943139/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree049.table
  base := (-3500714896033841304519582122227182703679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (842886)
      previous := (421443)
      next := (421443)
      square := (3120405041146323392373118634955000000000000)
      linear := (-150114820558187026007361270225972000000000000)
      constant := (1771100619320596245192873020396482194821242121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree049.table
  base := (-1750544829095012561075441376920766598409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (842886)
      previous := (421443)
      next := (421443)
      square := (3120405041146323392373118634955000000000000)
      linear := (-150508811093685299162963936720284500000000000)
      constant := (1780586328588946932203917797165697133137986782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346355085205895886277/100000000000000000000)
  centralHi := (173177542602947943139/50000000000000000000)
  directionLo := (174972176468967288383/50000000000000000000)
  directionHi := (349944352937934576767/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree050.table
  base := (-1386440837574092120374108326811824864117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-735568364706445234894321031000388489000000000000)
      constant := (8864066646471665234600063243918170440604005342415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree050.table
  base := (-1733213515634129842089971844347013212277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-368749459165193386678387048411259869500000000000)
      constant := (4455749317538283781631910815391363280178083936646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174972176468967288383/50000000000000000000)
  centralHi := (349944352937934576767/100000000000000000000)
  directionLo := (8837429464298288003/2500000000000000000)
  directionHi := (353497178571931520121/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree051.table
  base := (-6842035167796800591451345078891580619047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-83365040121386263433477026930628826000000000000)
      constant := (1025669805521149658665543984930576266087764618617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree051.table
  base := (-1710649629076423223549778571830936649361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-41791918099383152229610853861901850500000000000)
      constant := (515576639694399683556212856332848310666437872542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/2500000000000000000)
  centralHi := (353497178571931520121/100000000000000000000)
  directionLo := (357014650068428371059/100000000000000000000)
  directionHi := (17850732503421418553/5000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree052.table
  base := (-6731035989217966980172748096794345042417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-765002357478507506908265453750930379000000000000)
      constant := (9605707318438322924044460129467205959798489630183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree052.table
  base := (-3365762113331823698315881956515313361609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-383505066623703353454608321102973439500000000000)
      constant := (4828507781579538506268683807399317695396631328591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357014650068428371059/100000000000000000000)
  centralHi := (17850732503421418553/5000000000000000000)
  directionLo := (360497802307654412021/100000000000000000000)
  directionHi := (180248901153827206011/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree053.table
  base := (-3299651356734412147382591281475766481531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-389859676932269321457618832563100662000000000000)
      constant := (4994050796090476431206482821745294810340049720269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree053.table
  base := (-1649931441414800385946823568318434400311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-390882870352958336842718957448830224500000000000)
      constant := (5020702277783876953064727766543091580373134170978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360497802307654412021/100000000000000000000)
  centralHi := (180248901153827206011/50000000000000000000)
  directionLo := (72789524129180842869/20000000000000000000)
  directionHi := (181973810322952107173/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree054.table
  base := (-3223458419630746523817826032331880633043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-4903928087966480116803764669762174500000000000)
      constant := (64063019463420752358402640766797890206607714597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree054.table
  base := (-3223641667147564187209210185887086307283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-4916798445459423706553451775243049500000000000)
      constant := (64404596323574736593103614136361928298921835557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72789524129180842869/20000000000000000000)
  centralHi := (181973810322952107173/50000000000000000000)
  directionLo := (367365044171300169113/100000000000000000000)
  directionHi := (183682522085650084557/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree055.table
  base := (-3136973764250291451050470673088335566849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (16725366)
      previous := (8362683)
      next := (8362683)
      square := (61918119866052251777585602004355000000000000)
      linear := (-3343608870399177334418107801143567000000000000)
      constant := (44529042866058302337047659943735081473123639631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree055.table
  base := (-784283120520727953169340226222330320497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (16725366)
      previous := (8362683)
      next := (8362683)
      square := (61918119866052251777585602004355000000000000)
      linear := (-3352384114144366145611076282153254500000000000)
      constant := (44766256647851171931589837668966717407757691772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367365044171300169113/100000000000000000000)
  centralHi := (183682522085650084557/50000000000000000000)
  directionLo := (370750968689425874543/100000000000000000000)
  directionHi := (23171935543089117159/6250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree056.table
  base := (-3040226744202292827581082825222616216997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-8406840234924816846287288767877695500000000000)
      constant := (114097529308231928704510223559766366784403407747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree056.table
  base := (-304036418918393232718660925063297791819/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-8428903704912720143001038091559195500000000000)
      constant := (114704813370396650443061872088646640987767170690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370750968689425874543/100000000000000000000)
  centralHi := (23171935543089117159/6250000000000000000)
  directionLo := (187053124732864303733/50000000000000000000)
  directionHi := (374106249465728607467/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree057.table
  base := (-5866484563666069814637090637694838498303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-93176371045407020771458501180809456000000000000)
      constant := (1288310719553410791017599408750397693046710627233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree057.table
  base := (-733340320633559574780895863383707396513/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-46710453918886474488351278092473040500000000000)
      constant := (647580903120909665137664054112334685964475282172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187053124732864303733/50000000000000000000)
  centralHi := (374106249465728607467/100000000000000000000)
  directionLo := (188715851874239943789/50000000000000000000)
  directionHi := (377431703748479887579/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree058.table
  base := (-5632083083858691499728649236938665104323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-853304335794694322950098722002556049000000000000)
      constant := (12015743188799977963812748638598258810093385195077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree058.table
  base := (-352018069289350019737212070572527308691/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-427771888999233253783272139178114149500000000000)
      constant := (6039793383920463322789286002739142781851154728872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188715851874239943789/50000000000000000000)
  centralHi := (377431703748479887579/100000000000000000000)
  directionLo := (380728113093381387143/100000000000000000000)
  directionHi := (47591014136672673393/12500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree059.table
  base := (-2688642502074908253592205820362051785281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-434010666090362729478535466688913497000000000000)
      constant := (6222198582280173053217737410179254374178858666519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree059.table
  base := (-672182914508764391368545677121610466779/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-435149692728488237171382775523970934500000000000)
      constant := (6255231207220332391838222335093170724708210997684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380728113093381387143/100000000000000000000)
  centralHi := (47591014136672673393/12500000000000000000)
  directionLo := (76799245101709933009/20000000000000000000)
  directionHi := (191998112754274832523/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree060.table
  base := (-5102120871377627121941704165839773754549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-98082036507417399440449238305899771000000000000)
      constant := (1431195298269718391891420976527229952801492029739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree060.table
  base := (-2551137585339891235264815253195447366247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-49169721828638135617721490207758635500000000000)
      constant := (719393471689043726646306248601359903921394997817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76799245101709933009/20000000000000000000)
  centralHi := (191998112754274832523/50000000000000000000)
  directionLo := (96809189359139368223/25000000000000000000)
  directionHi := (387236757436557472893/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree061.table
  base := (-961323328502555850399820456273179218383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-897455324952787730971015356128368884000000000000)
      constant := (13324824137576685399645830558105876258244941745085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree061.table
  base := (-961350027917520317863816664951878768669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-899810600373996407895208096431369009000000000000)
      constant := (13395446396429695030057444721203534881440242947655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96809189359139368223/25000000000000000000)
  centralHi := (387236757436557472893/100000000000000000000)
  directionLo := (390450395588409629807/100000000000000000000)
  directionHi := (24403149724275601863/6250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree062.table
  base := (-35084331080392386826314120456741862527/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-456086160669409433488993783751819914500000000000)
      constant := (6888298002435178305804863212415486267397617156672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree062.table
  base := (-2245454928938965225962802488555382314939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-457283103916253187335714684561541289500000000000)
      constant := (6924776811700117435684557166387393560233010149261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390450395588409629807/100000000000000000000)
  centralHi := (24403149724275601863/6250000000000000000)
  directionLo := (39363779864275215577/10000000000000000000)
  directionHi := (393637798642752155771/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree063.table
  base := (-415467283123604448656373536931202222577/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (509894)
      previous := (254947)
      next := (254947)
      square := (1887652432298393163287442137195000000000000)
      linear := (-116766102006153943434739201168923000000000000)
      constant := (1793408017765213684056972544046470072611704835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree063.table
  base := (-1038693177077360121510292839670544166199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (509894)
      previous := (254947)
      next := (254947)
      square := (1887652432298393163287442137195000000000000)
      linear := (-117072539089319267000207941775610500000000000)
      constant := (1802897926269543287104952981441718187277212258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39363779864275215577/10000000000000000000)
  centralHi := (393637798642752155771/100000000000000000000)
  directionLo := (198399799411112190109/50000000000000000000)
  directionHi := (396799598822224380219/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree064.table
  base := (-474783493039747218299005601914008062643/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-470803157055440569495965995127090859500000000000)
      constant := (7351627141426646402833378518883410638217057331028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree064.table
  base := (-3798354312715914605744814267006431451033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-944077422749526308223871914506509719000000000000)
      constant := (14780996374795761686942978516787317242801569786367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198399799411112190109/50000000000000000000)
  centralHi := (396799598822224380219/100000000000000000000)
  directionLo := (24996025209852469769/6250000000000000000)
  directionHi := (79987280671527903261/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree065.table
  base := (-855398318481455873189589544849371498827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-478161655248456137499452100814726332000000000000)
      constant := (7589069999678873395448529189801299363144363543546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree065.table
  base := (-684333589732644352892191507673227012697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-958833030208036275000093187198223289000000000000)
      constant := (15258331219154267274129056403059068558092923219515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/6250000000000000000)
  centralHi := (79987280671527903261/20000000000000000000)
  directionLo := (201524397924798954969/50000000000000000000)
  directionHi := (403048795849597909939/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree066.table
  base := (-756165087190694193669316401683052587763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 108045000000000000000000000000000000000000000
      center := (1858374)
      previous := (929187)
      next := (929187)
      square := (6879791096228027975287289111595000000000000)
      linear := (-445840361286934532142275671719340500000000000)
      constant := (7190417687437037339072330529347839833262058666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree066.table
  base := (-1512362451413809992148696073987402821777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 108045000000000000000000000000000000000000000
      center := (1858374)
      previous := (929187)
      next := (929187)
      square := (6879791096228027975287289111595000000000000)
      linear := (-447010393786293040301338135853965500000000000)
      constant := (7228378331589906817673667329937971712424220807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201524397924798954969/50000000000000000000)
  centralHi := (403048795849597909939/100000000000000000000)
  directionLo := (10153433438404505239/2500000000000000000)
  directionHi := (406137337536180209561/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree067.table
  base := (-2607478974437601483578537265157383183003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-985757303268974547012848624379994554000000000000)
      constant := (16151023223746098047219522048744368993428553620397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree067.table
  base := (-2607534770783407339857830044423669976751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-988344245125056208552535732581650429000000000000)
      constant := (16236226510136427918510064096504468321949430141049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10153433438404505239/2500000000000000000)
  centralHi := (406137337536180209561/100000000000000000000)
  directionLo := (25575160529657443921/6250000000000000000)
  directionHi := (409202568474519102737/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree068.table
  base := (-1085028746018450924899077785622889808363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-500237149827502841509910417877632749500000000000)
      constant := (8324510152299156214950650105658831980328750403037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree068.table
  base := (-33907901740465194756379466811601558377/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-501549926291783087664378502636681999500000000000)
      constant := (8368393269479592762682287607793339536883494471136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25575160529657443921/6250000000000000000)
  centralHi := (409202568474519102737/100000000000000000000)
  directionLo := (103061252160823582199/25000000000000000000)
  directionHi := (412245008643294328797/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree069.table
  base := (-856201498841056903306041077515837879519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-56399516446724267723710724840585358000000000000)
      constant := (953040044378175251208577659060734768683138345409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree069.table
  base := (-107027791418940293053271835762103940549/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-56547525557893119005832126553615420500000000000)
      constant := (958060440522408543239986778706199118678319005912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103061252160823582199/25000000000000000000)
  centralHi := (412245008643294328797/100000000000000000000)
  directionLo := (83053031794504922017/20000000000000000000)
  directionHi := (207632579486262305043/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree070.table
  base := (-1234521528999759408998259022432703363047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-21018536580144243980280923642975661000000000000)
      constant := (360573970699877213119390633106560361642600041297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree070.table
  base := (-617278762637082378091349419752315216769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-10536847627557001111032648476089705500000000000)
      constant := (181236025945061040092575831147411692869461904519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83053031794504922017/20000000000000000000)
  centralHi := (207632579486262305043/50000000000000000000)
  directionLo := (209131751153215886743/50000000000000000000)
  directionHi := (418263502306431773487/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree071.table
  base := (-368209111762314137816929395178116492517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-522312644406549545520368734940539167000000000000)
      constant := (9094615740080648939694552554284799685459174960083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree071.table
  base := (-368224658895430056125148500962940562803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-523683337479548037828710411674252354500000000000)
      constant := (9142457130248150809566801025962550478625066680597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209131751153215886743/50000000000000000000)
  centralHi := (418263502306431773487/100000000000000000000)
  directionLo := (421240504304617860569/100000000000000000000)
  directionHi := (42124050430461786057/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree072.table
  base := (-218097453287534440165775156801948966229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-13078299817273212679601354089584559000000000000)
      constant := (231086931401550493053554205637168998984382184691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree072.table
  base := (-43624861852701753529738279894566547987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-13112620770587728918933853037533559000000000000)
      constant := (232301715834383982247802547223866061159561343865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421240504304617860569/100000000000000000000)
  centralHi := (42124050430461786057/10000000000000000000)
  directionLo := (26512288392894864009/6250000000000000000)
  directionHi := (84839322857263564829/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree073.table
  base := (160218530404987639664508138434346400913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-537029640792580681527340946315810112000000000000)
      constant := (9627277183412928257881299921510696353622411299513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree073.table
  base := (160206934344495583097491036691080511937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-538438944938058004604931684365965924500000000000)
      constant := (9677852311711199446065510256673728837514084383337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512288392894864009/6250000000000000000)
  centralHi := (84839322857263564829/20000000000000000000)
  directionLo := (427132266022061859361/100000000000000000000)
  directionHi := (213566133011030929681/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree074.table
  base := (219795537945176771140815906149695698371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-544388138985596249530827052003445584500000000000)
      constant := (9899385087767959202887991800340695223525803489142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree074.table
  base := (87916212644035101703946342749807119191/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-545816748667312987993042320711822709500000000000)
      constant := (9951355555151241884695720083005148304700167846955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427132266022061859361/100000000000000000000)
  centralHi := (213566133011030929681/50000000000000000000)
  directionLo := (215023939238348377897/50000000000000000000)
  directionHi := (86009575695339351159/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree075.table
  base := (364533780977013743115188888330234117133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-61305181908734646392701461965675673000000000000)
      constant := (1130593822567757255326435883676803472089484733274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree075.table
  base := (364529458822886418373369637186441055201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-61466061377396441264572550784186610500000000000)
      constant := (1136525465631460187023775468390104669252364894978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215023939238348377897/50000000000000000000)
  centralHi := (86009575695339351159/20000000000000000000)
  directionLo := (216471928253684928923/50000000000000000000)
  directionHi := (432943856507369857847/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree076.table
  base := (1028646841238998087953518856361699546031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-559105135371627385537799263378716529500000000000)
      constant := (10455155102438660732393936614873874116918810244231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree076.table
  base := (2057278758574314132339514646464483863947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1121144712251645909538527186807072559000000000000)
      constant := (21019946383980070594992399150672320147647657457347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216471928253684928923/50000000000000000000)
  centralHi := (432943856507369857847/100000000000000000000)
  directionLo := (27238786969985493351/6250000000000000000)
  directionHi := (435820591519767893617/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree077.table
  base := (535331174804889176332272703923436798403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (682668)
      previous := (341334)
      next := (341334)
      square := (2527270198614377623574922530790000000000000)
      linear := (-191082352357781397720116501624676000000000000)
      constant := (3622471635274014919548631617708143228264307535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree077.table
  base := (107065719723516313061757076673730774557/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (682668)
      previous := (341334)
      next := (341334)
      square := (2527270198614377623574922530790000000000000)
      linear := (-191583794857506472645428986253801000000000000)
      constant := (3641453039864621841196637649127292936105418325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27238786969985493351/6250000000000000000)
  centralHi := (435820591519767893617/100000000000000000000)
  directionLo := (109669615521405558327/25000000000000000000)
  directionHi := (438678462085622233309/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree078.table
  base := (3316220035507624308335532501059918521883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-127516029279479671454393661056441661000000000000)
      constant := (2450295681007953689634708178728487380300063739387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree078.table
  base := (3316208919312121980577376647087721511613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-127850658574296204787885525798944411000000000000)
      constant := (2463127156820802809830715396005058220471477883357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109669615521405558327/25000000000000000000)
  centralHi := (438678462085622233309/100000000000000000000)
  directionLo := (441517834524238696771/100000000000000000000)
  directionHi := (110379458631059674193/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree079.table
  base := (1987992375542041562411836449427928598751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-581180629950674089548257580441622947000000000000)
      constant := (11317695291077627550126392772374039110361956880951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree079.table
  base := (397597515907564657077012281392666195589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-582705767313587904933595502441106634500000000000)
      constant := (11376927182819156745573404937202084799702528306945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441517834524238696771/100000000000000000000)
  centralHi := (110379458631059674193/25000000000000000000)
  directionLo := (222169531725290442047/50000000000000000000)
  directionHi := (88867812690116176819/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree080.table
  base := (4655948815329611334911026527299208232447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1177078256287379315103487372258516839000000000000)
      constant := (23225822656424365315195736741174232575266797525847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree080.table
  base := (4655940539558729999583929660642452744273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1180167142085685776643412277573926839000000000000)
      constant := (23347304908511577373102637683739190107111233834873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222169531725290442047/50000000000000000000)
  centralHi := (88867812690116176819/20000000000000000000)
  directionLo := (447142492292228547167/100000000000000000000)
  directionHi := (13973202884132142099/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree081.table
  base := (1339027800486999158896486078976949339037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-7356760818971669451299133232307332000000000000)
      constant := (147061464985974722827704223250412344410352736554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree081.table
  base := (267805203133930890122617407112221578361/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-7376066355211084835923663890528644500000000000)
      constant := (147830222324197116923766030464614859251670160810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447142492292228547167/100000000000000000000)
  centralHi := (13973202884132142099/3125000000000000000)
  directionLo := (224964226888672227921/50000000000000000000)
  directionHi := (449928453777344455843/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree082.table
  base := (759558879643036015551835882311920307189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-603256124529720793558715897504529364500000000000)
      constant := (12214897287751778015754312840372112157459013171956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree082.table
  base := (759558109881237654843611787040723832119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-604839178501352855097927411478676989500000000000)
      constant := (12278713834837736015918804171231393715111658255676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224964226888672227921/50000000000000000000)
  centralHi := (449928453777344455843/100000000000000000000)
  directionLo := (452697270395612510761/100000000000000000000)
  directionHi := (226348635197806255381/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree083.table
  base := (340851378848239338606056766908572510773/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-610614622722736361562202003192164837000000000000)
      constant := (12521667191122225067603465378544118597028349013730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree083.table
  base := (1704255566458436842891406079201258568361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-612216982230607838486038047824533774500000000000)
      constant := (12587049925484102968194216926591658010667286585122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452697270395612510761/100000000000000000000)
  centralHi := (226348635197806255381/50000000000000000000)
  directionLo := (22772462741697736071/5000000000000000000)
  directionHi := (455449254833954721421/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree084.table
  base := (1894445047002714751421307121717447017319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (4589046)
      previous := (2294523)
      next := (2294523)
      square := (16988871890685538469586979234755000000000000)
      linear := (-1401299593913269681554848319455329500000000000)
      constant := (29098159561275876928364334638237764880582318318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree084.table
  base := (1894443901973332354976550309989493444581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (4589046)
      previous := (2294523)
      next := (2294523)
      square := (16988871890685538469586979234755000000000000)
      linear := (-1404976838911253564340473206735579500000000000)
      constant := (29250014224402053520396808033713271719392573482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22772462741697736071/5000000000000000000)
  centralHi := (455449254833954721421/100000000000000000000)
  directionLo := (229092355194346756381/50000000000000000000)
  directionHi := (458184710388693512763/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree085.table
  base := (4179364165511340961277798643581339988701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-625331619108767497569174214567435782000000000000)
      constant := (13146760807608102717286310314503458680275949660901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree085.table
  base := (1671744876352092383206675667822473450383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1253945179378235610524518641032494689000000000000)
      constant := (26430665742220329280110188934959513077757881414915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229092355194346756381/50000000000000000000)
  centralHi := (458184710388693512763/100000000000000000000)
  directionLo := (230451965677848618031/50000000000000000000)
  directionHi := (460903931355697236063/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree086.table
  base := (1831974309380920344171817679178485973917/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1265380234603566131145320640510142509000000000000)
      constant := (26930169017953564882980669970356854523069478006585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree086.table
  base := (9159868141992860811421016471269340199759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1268700786836745577300739913724208259000000000000)
      constant := (27070559429379122799620035740789521027718108939559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230451965677848618031/50000000000000000000)
  centralHi := (460903931355697236063/100000000000000000000)
  directionLo := (463607203399929486731/100000000000000000000)
  directionHi := (115901800849982371683/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree087.table
  base := (1996241888965592798340086027384558708959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-142233025665510807461365872431712606000000000000)
      constant := (3063835436895593704881314605993675012255846493755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree087.table
  base := (2495301627391154218883762320460105923217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-71303133016403085782053399245328990500000000000)
      constant := (1539899644359982104627713450912312021292540669026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463607203399929486731/100000000000000000000)
  centralHi := (115901800849982371683/25000000000000000000)
  directionLo := (233147401952857878861/50000000000000000000)
  directionHi := (466294803905715757723/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree088.table
  base := (5411370846050892980479294599226593240201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (16725366)
      previous := (8362683)
      next := (8362683)
      square := (61918119866052251777585602004355000000000000)
      linear := (-5350472013948877699005227534135059500000000000)
      constant := (116638724585568552644206410436134678079947530681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree088.table
  base := (2705684790496525787549800300548661875739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (16725366)
      previous := (8362683)
      next := (8362683)
      square := (61918119866052251777585602004355000000000000)
      linear := (-5364512403941179796913977103750559500000000000)
      constant := (117246149760054147971701592362575974620511192918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233147401952857878861/50000000000000000000)
  centralHi := (466294803905715757723/100000000000000000000)
  directionLo := (58620875288617886087/12500000000000000000)
  directionHi := (468967002308943088697/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree089.table
  base := (11684468005547951937426236334314810378581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1309531223761659539166237274635955344000000000000)
      constant := (28886326264231499733632284780667382836730654186781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree089.table
  base := (584223291244754138239641048868588120671/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-656483804606137738814701865899674484500000000000)
      constant := (14518341676641526636164904643336101310418422268710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58620875288617886087/12500000000000000000)
  centralHi := (468967002308943088697/100000000000000000000)
  directionLo := (235812030206159410599/50000000000000000000)
  directionHi := (471624060412318821199/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree090.table
  base := (314159703603924136644841920682444756283/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-8174371729306732562797589419822384500000000000)
      constant := (182430763394818453158269731888749545660801868860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree090.table
  base := (12566386264899469024032767616505676236079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-16391644650256610424760802524581019000000000000)
      constant := (366759739839966626875433151796292180565781907159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235812030206159410599/50000000000000000000)
  centralHi := (471624060412318821199/100000000000000000000)
  directionLo := (237133116342366273221/50000000000000000000)
  directionHi := (474266232684732546443/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree091.table
  base := (3367125475708434233356953505350285572799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-13662910372793079705920221401903033000000000000)
      constant := (308458607776209386745333597058298773154602293902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree091.table
  base := (6734250141742527338063780307743142546127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-13698763511523422563080064052885470500000000000)
      constant := (310062601617595490780487741315464056964634945623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237133116342366273221/50000000000000000000)
  centralHi := (474266232684732546443/100000000000000000000)
  directionLo := (476893766545690125933/100000000000000000000)
  directionHi := (238446883272845062967/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree092.table
  base := (14390809107071315354427697798069054138539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1353682212919752947187153908761768179000000000000)
      constant := (30911805936448758555343903293594113746867981594339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree092.table
  base := (179885096397868154187553940931230218849/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-678617215793902688979033774937244839500000000000)
      constant := (15536235721885737438897008811756880106489146265960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476893766545690125933/100000000000000000000)
  centralHi := (238446883272845062967/50000000000000000000)
  directionLo := (479506902635719640971/100000000000000000000)
  directionHi := (119876725658929910243/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree093.table
  base := (7666654804207321940825964515244032253947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-76022178294765782399673673340946618000000000000)
      constant := (1755687266089323952074998401774807192762540427483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree093.table
  base := (3066661681277443928814749631450037545589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-152443337671812816081587646951800361000000000000)
      constant := (3529616486600078546517729947447302574100192784105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479506902635719640971/100000000000000000000)
  centralHi := (119876725658929910243/25000000000000000000)
  directionLo := (482105875073585715363/100000000000000000000)
  directionHi := (120526468768396428841/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree094.table
  base := (8148001640298485811116690854006731835041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-691558102845907609600549165756155034500000000000)
      constant := (16150319059287201542716508825597853744395283655241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree094.table
  base := (1629600224513131383983295812228216171077/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-693372823252412655755255047628958409500000000000)
      constant := (16234182881270244660669054312853706804546171752385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482105875073585715363/100000000000000000000)
  centralHi := (120526468768396428841/25000000000000000000)
  directionLo := (484690911701090344689/100000000000000000000)
  directionHi := (48469091170109034469/10000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree095.table
  base := (17278890016249033691409052845675711225877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1397833202077846355208070542887581014000000000000)
      constant := (33006607920821839277102557727735744600510293965277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree095.table
  base := (4319722281088291917043586272564249350839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-700750626981667639143365683974815194500000000000)
      constant := (16588961795375165617891978399432124629776125733278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484690911701090344689/100000000000000000000)
  centralHi := (48469091170109034469/10000000000000000000)
  directionLo := (60907779289523086907/12500000000000000000)
  directionHi := (487262234316184695257/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree096.table
  base := (18281969724095978917818044239133099935349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-156950022051541943468338083806983551000000000000)
      constant := (3746697799355804618705449040164614741936857741461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree096.table
  base := (1828196895593825747268590678731413860901/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-78680936745658069170164035591185775500000000000)
      constant := (1883067881219816887794176215009738136882726873945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60907779289523086907/12500000000000000000)
  centralHi := (487262234316184695257/100000000000000000000)
  directionLo := (489820058895066892151/100000000000000000000)
  directionHi := (61227507361883361519/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree097.table
  base := (965262116328483610249980143742919422767/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-713633597424954313611007482819061452000000000000)
      constant := (17220827468445130506443699861953696478646070201670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree097.table
  base := (19305241665046431088238577834894861025947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1431012468880355211839173913333057529000000000000)
      constant := (34620260574398454051251351482210140231529651019347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489820058895066892151/100000000000000000000)
  centralHi := (61227507361883361519/12500000000000000000)
  directionLo := (123091148950973806319/25000000000000000000)
  directionHi := (492364595803895225277/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree098.table
  base := (5087176939443689772408710551017171343537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (842886)
      previous := (421443)
      next := (421443)
      square := (3120405041146323392373118634955000000000000)
      linear := (-300288253068708821996873631198124500000000000)
      constant := (7324184120644572029262924958278044592676012274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree098.table
  base := (20348707188136805863225094100706382304849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1685772)
      previous := (842886)
      next := (842886)
      square := (6240810082292646784746237269910000000000000)
      linear := (-602152468279410736616157928373499000000000000)
      constant := (14724298095202134371669079767741610252969825049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123091148950973806319/25000000000000000000)
  centralHi := (492364595803895225277/100000000000000000000)
  directionLo := (61862006250088016021/12500000000000000000)
  directionHi := (494896050000704128169/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree099.table
  base := (21412365961756036178442757711930692960323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1528842465828450661174953135910000000000000)
      linear := (-148627812225484226021422241443594000000000000)
      constant := (3663657976147374154678294917966319718797735523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree099.table
  base := (214123654712860140851662864553166968653/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (764421232914225330587476567955000000000000)
      linear := (-74508911529301864370554864744234500000000000)
      constant := (1841320238610008171516504896149418194586792650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61862006250088016021/12500000000000000000)
  centralHi := (494896050000704128169/100000000000000000000)
  directionLo := (497414621228071422399/100000000000000000000)
  directionHi := (310884138267544639/62500000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree100.table
  base := (2249621689102246299837761483788973913687/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-735709092004001017621465799881967869500000000000)
      constant := (18325996983214114959610380470022981016103195675435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree100.table
  base := (22496216468756200674526395829744485433951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1475279291255885112167837731408198239000000000000)
      constant := (36841819345281308307278050369031166659873307156151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497414621228071422399/100000000000000000000)
  centralHi := (310884138267544639/62500000000000000)
  directionLo := (24996025209852469769/5000000000000000000)
  directionHi := (499920504197049395381/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree101.table
  base := (23600260505289782357805391683480290361687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1486135180394033171249903811139206684000000000000)
      constant := (37404178573010705134807715675072265011954581183087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree101.table
  base := (23600260141775666989858894162715121937151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1490034898714395078944059004099911809000000000000)
      constant := (37597819809811725608470078077388365029164546699351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/5000000000000000000)
  centralHi := (499920504197049395381/100000000000000000000)
  directionLo := (12560347219070976059/2500000000000000000)
  directionHi := (502413888762839042361/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree102.table
  base := (6181124192602340236274236519046964525669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-83380676487781350403159779028582090500000000000)
      constant := (2120225869064680401877682226944756715757313903882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree102.table
  base := (24724496457500575478008693575610439956643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-167198945130322782857808919643513931000000000000)
      constant := (4262395634450193810525602043028909362639794929027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12560347219070976059/2500000000000000000)
  centralHi := (502413888762839042361/100000000000000000000)
  directionLo := (504894960092656028667/100000000000000000000)
  directionHi := (126223740023164007167/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree103.table
  base := (25868925657455666927746317842597139256053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1515569173166095443263848233889748574000000000000)
      constant := (38931655176208174787078025581347225878123429662653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree103.table
  base := (25868925388130827582209425818340155320921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1519546113631415012496501549483338949000000000000)
      constant := (39133042045347166859001435210945481528383132477121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504894960092656028667/100000000000000000000)
  centralHi := (126223740023164007167/25000000000000000000)
  directionLo := (31710243676638025687/6250000000000000000)
  directionHi := (507363898826208410993/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree104.table
  base := (1689596696371805750875142408370292307633/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-765143084776063289635410222632509759500000000000)
      constant := (19853473585783212012741997807121694741095788721864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree104.table
  base := (27033546910157224895677900239609041483373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1534301721089924979272722822175052519000000000000)
      constant := (39912263815144770119025826742616656641604071593973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31710243676638025687/6250000000000000000)
  centralHi := (507363898826208410993/100000000000000000000)
  directionLo := (101964176245835942207/20000000000000000000)
  directionHi := (127455220307294927759/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree105.table
  base := (14109180601596354147657536741500719589053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (4589046)
      previous := (2294523)
      next := (2294523)
      square := (16988871890685538469586979234755000000000000)
      linear := (-1751704269771153872197043828390352000000000000)
      constant := (45906963297904721996270167503815875210491457133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree105.table
  base := (5643672200744085128999355857020056510187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9178092)
      previous := (4589046)
      next := (4589046)
      square := (33977743781371076939173958469510000000000000)
      linear := (-3512601652037267451358149874981329000000000000)
      constant := (92288494374098004654113015279049156177200442535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101964176245835942207/20000000000000000000)
  centralHi := (127455220307294927759/25000000000000000000)
  directionLo := (512266079340086392029/100000000000000000000)
  directionHi := (51226607934008639203/10000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree106.table
  base := (5884673564742023152304924438636459029819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1559720162324188851284764868015561409000000000000)
      constant := (41280638547353524835640812897290630193089828508095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree106.table
  base := (29423367652065104139773191455826297523323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1563812936006944912825165367558479659000000000000)
      constant := (41493928656450226967348685376196198173404639023923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512266079340086392029/100000000000000000000)
  centralHi := (51226607934008639203/10000000000000000000)
  directionLo := (102939932222171198993/20000000000000000000)
  directionHi := (257349830555427997483/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree107.table
  base := (30648566988762861692108018424069701385823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1574437158710219987291737079390832354000000000000)
      constant := (42079037927024280604867429236265284942146165386423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree107.table
  base := (766214171026879635962488717687893896381/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-789284271732727439800693320125096614500000000000)
      constant := (21148185863615804275412871926070113845226217291620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102939932222171198993/20000000000000000000)
  centralHi := (257349830555427997483/50000000000000000000)
  directionLo := (129280447635362751683/25000000000000000000)
  directionHi := (517121790541451006733/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree108.table
  base := (6378791737188412738095387246643239682457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-19619187099953717571589003589704979000000000000)
      constant := (529446169968792886341336525369856520178935450485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree108.table
  base := (31893958558878125439417884127083861083819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-19670668529925491930587752011628479000000000000)
      constant := (532179694210394786527297311544971672405932179699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129280447635362751683/25000000000000000000)
  centralHi := (517121790541451006733/100000000000000000000)
  directionLo := (64941578476105478677/12500000000000000000)
  directionHi := (519532627808843829417/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree109.table
  base := (33159542904819499679120886849851785815067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1603871151482282259305681502141374244000000000000)
      constant := (43698944068451955383982686452007907195634105472467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree109.table
  base := (16579771397753996287350747356581293417177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-804039879191237406576914592816810184500000000000)
      constant := (21962239583823407068099178708504067912532986016577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64941578476105478677/12500000000000000000)
  centralHi := (519532627808843829417/100000000000000000000)
  directionLo := (260966164695314941097/50000000000000000000)
  directionHi := (104386465878125976439/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree110.table
  base := (17222659818325294066178988183055245183617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (16725366)
      previous := (8362683)
      next := (8362683)
      square := (61918119866052251777585602004355000000000000)
      linear := (-6688380776315344608729974022796054500000000000)
      constant := (183968805081643372420444131974848324638555017777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree110.table
  base := (8611329885654656939434399831690456035239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (16725366)
      previous := (8362683)
      next := (8362683)
      square := (61918119866052251777585602004355000000000000)
      linear := (-6705931263805722231115910984815429500000000000)
      constant := (184917948499378984876377772821507415660378631918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260966164695314941097/50000000000000000000)
  centralHi := (104386465878125976439/20000000000000000000)
  directionLo := (524321048183548788529/100000000000000000000)
  directionHi := (52432104818354878853/10000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree111.table
  base := (1430051554964856421710061263850750575399/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-181478349361593836813291769432435126000000000000)
      constant := (5038851116801925935392002136055198153405985897775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree111.table
  base := (35751288793239453751035972288566817713153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-181954552588832749634030192335227501000000000000)
      constant := (5064838704276293921747514258479076155039586304417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524321048183548788529/100000000000000000000)
  centralHi := (52432104818354878853/10000000000000000000)
  directionLo := (822967083776824507/156250000000000000)
  directionHi := (526698933617167684481/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree112.table
  base := (18538725305566629968896886554922536527079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-16816552455514037421699980982318235500000000000)
      constant := (471291548292728074122521936450373639244593162671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree112.table
  base := (37077450541567607325424338031926467433783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-33721358790979688030254959259362471000000000000)
      constant := (947442725967776588964216087250346646058606851967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (822967083776824507/156250000000000000)
  centralHi := (526698933617167684481/100000000000000000000)
  directionLo := (529066131762965840291/100000000000000000000)
  directionHi := (132266532940741460073/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree113.table
  base := (38423804842619163413519712728692207296663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1662739137026406803333570347642458024000000000000)
      constant := (47031185874048512637347213782062010426863740345263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree113.table
  base := (38423804782791006088498889914899734150409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1667102188216514680258714276400474649000000000000)
      constant := (47273579238539698140553693618607403810873988820209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529066131762965840291/100000000000000000000)
  centralHi := (132266532940741460073/25000000000000000000)
  directionLo := (531422785439045935551/100000000000000000000)
  directionHi := (8303481022485092743/1562500000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree114.table
  base := (9947587891096912002650398875574245035459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-93192007411802107741141253278762720500000000000)
      constant := (2660194581955676830799069205549930186355038514502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree114.table
  base := (39790351512937761021878205920638060599949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-186873088408336071892770616565798691000000000000)
      constant := (5347800592972123760990966670974070469032020050861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531422785439045935551/100000000000000000000)
  centralHi := (8303481022485092743/1562500000000000000)
  directionLo := (533769034310684393827/100000000000000000000)
  directionHi := (133442258577671098457/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree115.table
  base := (41177090772989719005639062883795017057851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1692173129798469075347514770392999914000000000000)
      constant := (48743521536067199778036248884849935047328778360051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree115.table
  base := (164708362914992105210939315350416632277/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-848306701566767306905578410891950894500000000000)
      constant := (24497285933486294318604910712161940945560681459625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533769034310684393827/100000000000000000000)
  centralHi := (133442258577671098457/25000000000000000000)
  directionLo := (53610501498692109741/10000000000000000000)
  directionHi := (536105014986921097411/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree116.table
  base := (42584022465605615857238464310897116896281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1706890126184500211354486981768270859000000000000)
      constant := (49611243056577207936474279131760033004123780644481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree116.table
  base := (21292011213782478764058456708157360742851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-855684505296022290293689047237807679500000000000)
      constant := (24933339414573800554455534979773705269630279045051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53610501498692109741/10000000000000000000)
  centralHi := (536105014986921097411/100000000000000000000)
  directionLo := (67303857639172188009/12500000000000000000)
  directionHi := (538430861113377504073/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree117.table
  base := (22005573319974209492847993666466061779867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-10627204460311921897292957982367542000000000000)
      constant := (311646092819002414681956239540577413546848740707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree117.table
  base := (44011146607241943017450340566415557155487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-21310180469759932683501226755152209000000000000)
      constant := (626500323743501688475138613316111952080369238727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67303857639172188009/12500000000000000000)
  centralHi := (538430861113377504073/100000000000000000000)
  directionLo := (33796668966342601127/6250000000000000000)
  directionHi := (540746703461481618033/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree118.table
  base := (45458463294182013349507761927415622561959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1736324118956562483368431404518812749000000000000)
      constant := (51369793476327541675828351494643481257668154141759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree118.table
  base := (2272923163303184660606235949472240819307/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-870440112754532257069910319929521249500000000000)
      constant := (25817057024580165535634436786386399707303370047070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33796668966342601127/6250000000000000000)
  centralHi := (540746703461481618033/100000000000000000000)
  directionLo := (543052670014268373753/100000000000000000000)
  directionHi := (271526335007134186877/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree119.table
  base := (46925972426851283543963404103506555014987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-35735532966175379987253135018246606000000000000)
      constant := (1066543313785518721639729797879799996664392491763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree119.table
  base := (5865746550334891399179591570423190255767/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-17914651356811984499143284821946490500000000000)
      constant := (536014717417611124588179801507150616288567383932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543052670014268373753/100000000000000000000)
  centralHi := (271526335007134186877/50000000000000000000)
  directionLo := (136337221512228681289/25000000000000000000)
  directionHi := (545348886048914725157/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree120.table
  base := (24206837018411364683730196100107489453247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-98097672873812486410131990403853035500000000000)
      constant := (2953286318563352470969693641563357086491020945183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree120.table
  base := (3025854626002770766030877184800972613643/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-98355080023671358205125732513470535500000000000)
      constant := (2968472833138652685312226457008684072257548816216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136337221512228681289/25000000000000000000)
  centralHi := (545348886048914725157/100000000000000000000)
  directionLo := (547635474216160049671/100000000000000000000)
  directionHi := (68454434277020006209/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree121.table
  base := (49921568123233958554521070032648073569941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (33450732)
      previous := (16725366)
      next := (16725366)
      square := (123836239732104503555171204008710000000000000)
      linear := (-14714670314997156127184694534253104000000000000)
      constant := (446821384729396934206772415573408044620955695621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree121.table
  base := (1248039202634350504675168802888128979203/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (16725366)
      previous := (8362683)
      next := (8362683)
      square := (61918119866052251777585602004355000000000000)
      linear := (-7376640693737993448216877925347864500000000000)
      constant := (224559174040708372609458893469550036240087572860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547635474216160049671/100000000000000000000)
  centralHi := (68454434277020006209/12500000000000000000)
  directionLo := (274956277308377167459/50000000000000000000)
  directionHi := (549912554616754334919/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree122.table
  base := (2572482734272537076914493825764690960713/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-897596052250343513698160125009948264500000000000)
      constant := (27489661914912773113697151151701995162903814193130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree122.table
  base := (25724827335050174549096866563811586050763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-899951327671552190622352865312948389500000000000)
      constant := (27630934835489780526851895620927595580575351119363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274956277308377167459/50000000000000000000)
  centralHi := (549912554616754334919/100000000000000000000)
  directionLo := (552180244875068977881/100000000000000000000)
  directionHi := (276090122437534488941/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree123.table
  base := (2119917348921220301509175079497655494309/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-201101011209635351489254717932796386000000000000)
      constant := (6211218062981720153111433967138340479793982622525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree123.table
  base := (52997933709837888107624865949911675426253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-201628695866846038668991889257512261000000000000)
      constant := (6243128850652342549474148947530611801708594030317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552180244875068977881/100000000000000000000)
  centralHi := (276090122437534488941/50000000000000000000)
  directionLo := (277219330104998928551/50000000000000000000)
  directionHi := (554438660209997857103/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree124.table
  base := (6820800654461415869508431966669846518229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-912313048636374649705132336385219209500000000000)
      constant := (28415151881640100033453091054343865476124459968116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree124.table
  base := (5456640522435388663171571327192681877313/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-914706935130062157398574138004661959500000000000)
      constant := (28561095036260257356331961899065159601329934279565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277219330104998928551/50000000000000000000)
  centralHi := (554438660209997857103/100000000000000000000)
  directionLo := (55668791350326960539/10000000000000000000)
  directionHi := (556687913503269605391/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree125.table
  base := (11231013844657113255678990128176003446897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1839343093658780435417236884145709364000000000000)
      constant := (57767347419156228152556952617166916398070365151485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree125.table
  base := (11231013842708606957939620382066293342559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1844169477718634281573369548701037489000000000000)
      constant := (58063960920925378182612018367166530801310301211795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55668791350326960539/10000000000000000000)
  centralHi := (556687913503269605391/100000000000000000000)
  directionLo := (279464057682642841979/50000000000000000000)
  directionHi := (558928115365285683959/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree126.table
  base := (14440981421444380497330494805671806615293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (509894)
      previous := (254947)
      next := (254947)
      square := (1887652432298393163287442137195000000000000)
      linear := (-233567660625448673648804370813930500000000000)
      constant := (7396333274686662314519357007007391782844144394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree126.table
  base := (28881962838703024932710849517671501347201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (509894)
      previous := (254947)
      next := (254947)
      square := (1887652432298393163287442137195000000000000)
      linear := (-234180534791779320779741852027305500000000000)
      constant := (7434299848965191513527254806817434831487554729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279464057682642841979/50000000000000000000)
  centralHi := (558928115365285683959/100000000000000000000)
  directionLo := (561159374198592911199/100000000000000000000)
  directionHi := (701449217748241139/125000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree127.table
  base := (5939297462322444258180083255721387912393/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-934388543215421353715590653448125627000000000000)
      constant := (29832271054600519575121196209564606537329512334965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree127.table
  base := (29696487308015759488597960294787922853461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-936840346317827107562906047042232314500000000000)
      constant := (29985361956501767758919991311167663424460137797661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561159374198592911199/100000000000000000000)
  centralHi := (701449217748241139/125000000000000000)
  directionLo := (281690898129546752453/50000000000000000000)
  directionHi := (563381796259093504907/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree128.table
  base := (30521108017880217562250170900565142896499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-941747041408436921719076759135761099500000000000)
      constant := (30312346571687162539907798923447177972234136664299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree128.table
  base := (7630277003697564076302283739813135721037/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-944218150047082090951016683388089099500000000000)
      constant := (30467858028341352188015730939123005264910890449748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281690898129546752453/50000000000000000000)
  centralHi := (563381796259093504907/100000000000000000000)
  directionLo := (8837429464298288003/1562500000000000000)
  directionHi := (565595485715090432193/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree129.table
  base := (6271164992358282733738855102267494639229/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-105456171066828054413618096091488508000000000000)
      constant := (3421808146499290377607968440639486148766255173905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree129.table
  base := (3135582495913677782648351358661554482547/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-105732883752926341593236368859327320500000000000)
      constant := (3439358257340465902496713365349936274284163328830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/1562500000000000000)
  centralHi := (565595485715090432193/100000000000000000000)
  directionLo := (56780054470426090457/10000000000000000000)
  directionHi := (567800544704260904571/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree130.table
  base := (16100319071735154900505321734391516498077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-956464037794468057726048970511032044500000000000)
      constant := (31284051295022801914326871539986923967855128154954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree130.table
  base := (32200638141189801947134952947376797422377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-958973757505592057727237956079802669500000000000)
      constant := (31444460819673455123132522673255540817179657461777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56780054470426090457/10000000000000000000)
  centralHi := (567800544704260904571/100000000000000000000)
  directionLo := (284998536694323093319/50000000000000000000)
  directionHi := (569997073388646186639/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree131.table
  base := (13222219025224943086149336531644559632969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1927645071974967251459070152397335034000000000000)
      constant := (63551361002556301774870713542659850836322563673845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree131.table
  base := (66111095122206726185554771571138683575621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1932703122469694082230697184851318909000000000000)
      constant := (63877135078345525918133009416348830769776912071821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284998536694323093319/50000000000000000000)
  centralHi := (569997073388646186639/100000000000000000000)
  directionLo := (286092585003870743279/50000000000000000000)
  directionHi := (572185170007741486559/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree132.table
  base := (67841106441459665023446155563581197948889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (3716748)
      previous := (1858374)
      next := (1858374)
      square := (13759582192456055950574578223190000000000000)
      linear := (-1783619897484847004101049002546011000000000000)
      constant := (59267513199749272742086816353989693106477542401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree132.table
  base := (67841106438094236956782352875872982074039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (3716748)
      previous := (1858374)
      next := (1858374)
      square := (13759582192456055950574578223190000000000000)
      linear := (-1788300027482281036737298859084511000000000000)
      constant := (59571247887173753972371688774162581269637908751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286092585003870743279/50000000000000000000)
  centralHi := (572185170007741486559/100000000000000000000)
  directionLo := (143591232732441386951/25000000000000000000)
  directionHi := (114872986185953109561/20000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree133.table
  base := (34795655116648347916242514325058909609299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-19970194538234995137479740562733438000000000000)
      constant := (668785563326182017422908267210832973093456235451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree133.table
  base := (69591310230406061691428399678455871871911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-40045190558912530934349790412954001000000000000)
      constant := (1344424147994194911984295874432827052010613385839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143591232732441386951/25000000000000000000)
  centralHi := (114872986185953109561/20000000000000000000)
  directionLo := (288268225350592824077/50000000000000000000)
  directionHi := (115307290140237129631/20000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree134.table
  base := (17840426625501959385655864958570316082707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-985898030566530329739993393261573934500000000000)
      constant := (33273675498440847763063928873521013631883587496214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree134.table
  base := (14272341299905030050005448823084873449641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-1976969944845223982559361002926459619000000000000)
      constant := (66888217986104535405177211604023002871382576949205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288268225350592824077/50000000000000000000)
  centralHi := (115307290140237129631/20000000000000000000)
  directionLo := (144674955523642504693/25000000000000000000)
  directionHi := (578699822094570018773/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree135.table
  base := (73152295247980977410386791456954559528369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-24524852561964096240579740714795294000000000000)
      constant := (834091595645477275469962698866610288713741290249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree135.table
  base := (292609180983395121755750248166151924477/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-12294602174714407094664088121099834500000000000)
      constant := (419181439211780994141635690023546485406372814625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144674955523642504693/25000000000000000000)
  centralHi := (578699822094570018773/100000000000000000000)
  directionLo := (580855136154836209339/100000000000000000000)
  directionHi := (29042756807741810467/5000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree136.table
  base := (74963076471615706227724841742115717146791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2001230053905122931493931209273689759000000000000)
      constant := (68583189957181132319096285074481963335157432316991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree136.table
  base := (37481538234892308825325324510428559916783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1003240579881121958055901774154943379500000000000)
      constant := (34467154375168550444245328722273493350102280829383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580855136154836209339/100000000000000000000)
  centralHi := (29042756807741810467/5000000000000000000)
  directionLo := (7287531028049507897/1250000000000000000)
  directionHi := (583002482243960631761/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree137.table
  base := (2399814067916244871894354343880227641571/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1007973525145577033750451710324480352000000000000)
      constant := (34806331563291855627978766139461764525407775644336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree137.table
  base := (76794050171747416359685224083177080707283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2021236767220753882888024821001600329000000000000)
      constant := (69968964780200035003474262460692038989797005719883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7287531028049507897/1250000000000000000)
  centralHi := (583002482243960631761/100000000000000000000)
  directionLo := (292570974042105701387/50000000000000000000)
  directionHi := (23405677923368456111/4000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree138.table
  base := (39322608176753243647759733221849430417247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-112814669259843622417104201779123980500000000000)
      constant := (3924991041972284320384294253160123794368241141183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree138.table
  base := (7864521635215626625785947274461355012153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-113110687482181324981347005205184105500000000000)
      constant := (3945075624550399194375593912737233920876856577085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292570974042105701387/50000000000000000000)
  centralHi := (23405677923368456111/4000000000000000000)
  directionLo := (587273619799963663713/100000000000000000000)
  directionHi := (293636809899981831857/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree139.table
  base := (80516575012591662057566964562397704565191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2045381043063216339514847843399502594000000000000)
      constant := (71694716843943141286305384019333606484891692215391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree139.table
  base := (16103315002286460058502599574490234349211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2050747982137773816440467366385027469000000000000)
      constant := (72061498135468462559514459300214620017213687217055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587273619799963663713/100000000000000000000)
  centralHi := (293636809899981831857/50000000000000000000)
  directionLo := (147349395489538443291/25000000000000000000)
  directionHi := (117879516391630754633/20000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree140.table
  base := (82408126150992224930153507032366440608493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-42042817131617295418812654179077011000000000000)
      constant := (1484638722284073297123532672507265115735788154757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree140.table
  base := (20602031537499198551054588069952152468293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-21076567240778405951190700398742255500000000000)
      constant := (746116076131569180929991288177619297541490489914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147349395489538443291/25000000000000000000)
  centralHi := (117879516391630754633/20000000000000000000)
  directionLo := (591513917607426135697/100000000000000000000)
  directionHi := (295756958803713067849/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree141.table
  base := (84319869769124234034118384276047882425373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-230535003981697623503199140683338276000000000000)
      constant := (8200842266604473260943079980929742228275916103997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree141.table
  base := (84319869768269597664570643352174112966809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-231139910783865972221434434640939401000000000000)
      constant := (8242777024243668555610723478939813105259072857401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591513917607426135697/100000000000000000000)
  centralHi := (295756958803713067849/50000000000000000000)
  directionLo := (118724541663204787597/20000000000000000000)
  directionHi := (296811354158011968993/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree142.table
  base := (43125902933700782938494569193294902875279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1044766016110654873767882238762657714500000000000)
      constant := (37437782933257442039886778389720294408236543359079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree142.table
  base := (86251805866667846060603357525709181765031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2095014804513303716769131184460168179000000000000)
      constant := (75258351407375990481358439303916026485840244263231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118724541663204787597/20000000000000000000)
  centralHi := (296811354158011968993/50000000000000000000)
  directionLo := (119144806841694540831/20000000000000000000)
  directionHi := (148931008552118176039/25000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree143.table
  base := (88203934446234789796868681048916504973909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (33450732)
      previous := (16725366)
      next := (16725366)
      square := (123836239732104503555171204008710000000000000)
      linear := (-17390487839730089946634187511575094000000000000)
      constant := (627696312340108490521481706467186810928830796229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree143.table
  base := (17640786889120981918196323710348831683781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (33450732)
      previous := (16725366)
      next := (16725366)
      square := (123836239732104503555171204008710000000000000)
      linear := (-17436119107205071764837623612825469000000000000)
      constant := (630904545689689484994440725996578482673467063305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119144806841694540831/20000000000000000000)
  centralHi := (148931008552118176039/25000000000000000000)
  directionLo := (119563594800220669421/20000000000000000000)
  directionHi := (298908987000551673553/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree144.table
  base := (22544063876507563326349849670672113242091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-13080037191317111231788326544912699500000000000)
      constant := (475522494934349082838177329722110164022411038822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree144.table
  base := (90176255505489542826945121145680587290971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-26228716289263254942241650985723399000000000000)
      constant := (955904803474468487705348867292465365900360185891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119563594800220669421/20000000000000000000)
  centralHi := (298908987000551673553/50000000000000000000)
  directionLo := (74988075629557409307/12500000000000000000)
  directionHi := (599904605036459274457/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree145.table
  base := (92168769047189345553157682672892607549327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2133683021379403155556681111651128264000000000000)
      constant := (78125737025158601850000462484723497637889880378727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree145.table
  base := (92168769046725203415486416674535778107479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2139281626888833617097795002535308889000000000000)
      constant := (78524868566324044187220246283498597292116595431279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74988075629557409307/12500000000000000000)
  centralHi := (599904605036459274457/100000000000000000000)
  directionLo := (60198400331663009989/10000000000000000000)
  directionHi := (601984003316630099891/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree146.table
  base := (94181475070107911046709279363325520537467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2148400017765434291563653323026399209000000000000)
      constant := (79224532330544593736239742654431792881717301474867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree146.table
  base := (94181475069709513306139341263253899502393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2154037234347343583874016275227022459000000000000)
      constant := (79629188483138074653226734032005951656124112056993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60198400331663009989/10000000000000000000)
  centralHi := (601984003316630099891/100000000000000000000)
  directionLo := (151014060883888151587/25000000000000000000)
  directionHi := (604056243535552606349/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree147.table
  base := (4810718678758789496270752499564508386183/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (93654)
      previous := (46827)
      next := (46827)
      square := (346711671238480376930346514995000000000000)
      linear := (-50051298397692290887376221352253000000000000)
      constant := (1858740110498674183789621817813782558825532870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree147.table
  base := (48107186787416919943789755877820906186769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (93654)
      previous := (46827)
      next := (46827)
      square := (346711671238480376930346514995000000000000)
      linear := (-50182628576191715272577110183690500000000000)
      constant := (1868231959643742159244015947882345466837391441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151014060883888151587/25000000000000000000)
  centralHi := (604056243535552606349/100000000000000000000)
  directionLo := (121224279822063560197/20000000000000000000)
  directionHi := (303060699555158900493/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree148.table
  base := (24566866140694116166334952220235788012259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1088917005268748281788798872888470549500000000000)
      constant := (40722615160064473726523798293980007605295738504118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree148.table
  base := (98267464562482977829572055491456217995313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2183548449264363517426458820610449599000000000000)
      constant := (81861049612568621207676329493568111466565522573913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121224279822063560197/20000000000000000000)
  centralHi := (303060699555158900493/50000000000000000000)
  directionLo := (152044885552880296803/25000000000000000000)
  directionHi := (608179542211521187213/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree149.table
  base := (6271296752080424756802893353683836317679/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1096275503461763849792284978576106022000000000000)
      constant := (41283566502172600917707207254112213969242276651832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree149.table
  base := (100340748033034915327878744714146026432383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2198304056722873484202680093302163169000000000000)
      constant := (82988590825203087255830372178521727583358149664983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152044885552880296803/25000000000000000000)
  centralHi := (608179542211521187213/100000000000000000000)
  directionLo := (24409229751707670053/4000000000000000000)
  directionHi := (305115371896345875663/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree150.table
  base := (102434223987076834299696309277744864006273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-245252000367728759510171352058609221000000000000)
      constant := (9299637572021019123792243452592597465723697944097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree150.table
  base := (102434223986860670919733605236426041415371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-245895518242375938997655707332652971000000000000)
      constant := (9347096941088375296162547374433783094802314984619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24409229751707670053/4000000000000000000)
  centralHi := (305115371896345875663/50000000000000000000)
  directionLo := (153068768404708403797/25000000000000000000)
  directionHi := (612275073618833615189/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree151.table
  base := (20909578484901938360250723143200585925541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2221984999695589971598514379902753934000000000000)
      constant := (84834045751669403127021627519220194683713009228705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree151.table
  base := (816780409565032727652037810467340898201/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1113907635819946708877561319342795154500000000000)
      constant := (42633447273177028426254280302190709626427134105664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153068768404708403797/25000000000000000000)
  centralHi := (612275073618833615189/100000000000000000000)
  directionLo := (307156300147056418811/50000000000000000000)
  directionHi := (614312600294112837623/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree152.table
  base := (106681753345941469046388606584301783193443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2236701996081621107605486591278024879000000000000)
      constant := (85979055814794274701051216955278310724766522558043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree152.table
  base := (21336350669156457014461657744474327367851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2242570879098403384531343911377303879000000000000)
      constant := (86417657054887521461273159199369772822800353350255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307156300147056418811/50000000000000000000)
  centralHi := (614312600294112837623/100000000000000000000)
  directionLo := (308171695644360225553/50000000000000000000)
  directionHi := (616343391288720451107/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree153.table
  base := (108835806751721222860251923935667961439277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-27795296203304348686573565464855504000000000000)
      constant := (1075700843673728406315911433896032079450300193317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree153.table
  base := (21767161350316925877218471337295791981591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-27868228229097695695155125729247129000000000000)
      constant := (1081187160437086419903649160700207625911418994555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308171695644360225553/50000000000000000000)
  centralHi := (616343391288720451107/100000000000000000000)
  directionLo := (123673502592988298639/20000000000000000000)
  directionHi := (154591878241235373299/25000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree154.table
  base := (6938128290136935665775331941950501178779/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (341334)
      previous := (170667)
      next := (170667)
      square := (1263635099307188811787461265395000000000000)
      linear := (-191106087776495478126111571430980500000000000)
      constant := (7445790463822788849811246530223739313428590808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree154.table
  base := (27752513160518441678600575433504674136497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (341334)
      previous := (170667)
      next := (170667)
      square := (1263635099307188811787461265395000000000000)
      linear := (-191607530276220553051424056060105500000000000)
      constant := (7483758084661119356927384283143599603295513186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123673502592988298639/20000000000000000000)
  centralHi := (154591878241235373299/25000000000000000000)
  directionLo := (620385030602458529773/100000000000000000000)
  directionHi := (310192515301229264887/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree155.table
  base := (113204491017685723927983091340063551303543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2280852985239714515626403225403837714000000000000)
      constant := (89460300762118046067546156013772810965173785888143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree155.table
  base := (113204491017585161365635112578507209304007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2286837701473933284860007729452444589000000000000)
      constant := (89916387172418075641554705563970930474290962829407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620385030602458529773/100000000000000000000)
  centralHi := (310192515301229264887/50000000000000000000)
  directionLo := (622396008422916966347/100000000000000000000)
  directionHi := (155599002105729241587/25000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree156.table
  base := (115419121878533545748531291204169288007859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-255063331291749516848152826308789851000000000000)
      constant := (10070680073766885401882998509574588432491980840851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree156.table
  base := (23083824375689453053554481407826571145051/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-255732589881382583515136555793795351000000000000)
      constant := (10122012378770144014479225686100613213403411270695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622396008422916966347/100000000000000000000)
  centralHi := (155599002105729241587/25000000000000000000)
  directionLo := (312200254806889150359/50000000000000000000)
  directionHi := (624400509613778300719/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree157.table
  base := (58826972612527813803719313776583654754297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1155143489005888393820173824077189802000000000000)
      constant := (45909821512684978086023083264783853908805222617697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree157.table
  base := (29413486306245400963514150535527904825927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1158174458195476609206225137417935864500000000000)
      constant := (46143788038729390500920786150753653113945168350654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312200254806889150359/50000000000000000000)
  centralHi := (624400509613778300719/100000000000000000000)
  directionLo := (626398596351486382353/100000000000000000000)
  directionHi := (313199298175743191177/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree158.table
  base := (119908961057566381894171952205031722274911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2325003974397807923647319859529650549000000000000)
      constant := (93010867846529407548389520083779828826949382909111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree158.table
  base := (119908961057502876270436727056297414820381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2331104523849463185188671547527585299000000000000)
      constant := (93484781178007935819697329833932625658333584588581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626398596351486382353/100000000000000000000)
  centralHi := (313199298175743191177/50000000000000000000)
  directionLo := (628390329823970707627/100000000000000000000)
  directionHi := (157097582455992676907/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree159.table
  base := (122184169376373546724384475186187073859031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (449726508)
      previous := (224863254)
      next := (224863254)
      square := (1664909445287182770019523965005990000000000000)
      linear := (-259968996753759895517143563433880166000000000000)
      constant := (10467755014154173833463328870382744076086395906359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree159.table
  base := (61092084688159533429803025165537013860561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (224863254)
      previous := (112431627)
      next := (112431627)
      square := (832454722643591385009761982502995000000000000)
      linear := (-130325562850442952886938490012183270500000000000)
      constant := (5260540372810333785185411924946253048734056380529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628390329823970707627/100000000000000000000)
  centralHi := (157097582455992676907/25000000000000000000)
  directionLo := (630375770252509793119/100000000000000000000)
  directionHi := (3939848564078186207/625000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree160.table
  base := (124479570181778300425166975127279292454887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2354437967169870195661264282280192439000000000000)
      constant := (95416424867951514419317429726545176133186184316287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree160.table
  base := (24895914036346313072756516886229260286281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2360615738766483118741114092911012439000000000000)
      constant := (95902412675200090306755039201947033665690410172405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630375770252509793119/100000000000000000000)
  centralHi := (3939848564078186207/625000000000000000)
  directionLo := (63235497691297672859/10000000000000000000)
  directionHi := (632354976912976728591/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree161.table
  base := (126795163474075383399715836030960645973149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (82602828)
      previous := (41301414)
      next := (41301414)
      square := (305799694032339692452565626225590000000000000)
      linear := (-48350101297059210850372173339907416000000000000)
      constant := (1972056266698534554964138124773568670892958834101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree161.table
  base := (63397581737017646850992371655372365342153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (41301414)
      previous := (20650707)
      next := (20650707)
      square := (152899847016169846226282813112795000000000000)
      linear := (-24238483124744827403238115975538020500000000000)
      constant := (991049378284256352059467862577022641083203636097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63235497691297672859/10000000000000000000)
  centralHi := (632354976912976728591/100000000000000000000)
  directionLo := (15858200203912202869/2500000000000000000)
  directionHi := (634328008156488114761/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree162.table
  base := (129130949253553225464963589892759531399899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (184989938365242530002169329445110000000000000)
      linear := (-29430518023974474909570477839885609000000000000)
      constant := (1208059157138572693967560796813351459821830057379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree162.table
  base := (32282737313379709382102923139198279923451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (92494969182621265001084664722555000000000000)
      linear := (-14753870084466068224034300236385429500000000000)
      constant := (607104974694838862803556666046048668463281815942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15858200203912202869/2500000000000000000)
  centralHi := (634328008156488114761/100000000000000000000)
  directionLo := (79536865178684592027/12500000000000000000)
  directionHi := (636294921429476736217/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree163.table
  base := (8217932970030879816814313254294264812697/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1199294478163981801841090458203002637000000000000)
      constant := (49541264423973370723991935052013492309319405248776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree163.table
  base := (131486927520464581076006740361869273877667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2404882561142013019069777910986153149000000000000)
      constant := (99586913161327055246328880052674717685613309255067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79536865178684592027/12500000000000000000)
  centralHi := (636294921429476736217/100000000000000000000)
  directionLo := (12765115465864150089/2000000000000000000)
  directionHi := (638255773293207504451/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree164.table
  base := (133863098275174143061020894327126613251091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2413305952713994739689153127781276219000000000000)
      constant := (100319968427401752611103507559100662146473936881291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree164.table
  base := (33465774568787211010332625900903407611541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1209819084300261492922999591838933359500000000000)
      constant := (50415280427076551664462837218620673091999425463482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12765115465864150089/2000000000000000000)
  centralHi := (638255773293207504451/100000000000000000000)
  directionLo := (320105309721377714103/50000000000000000000)
  directionHi := (640210619442755428207/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree165.table
  base := (136259461517863717910866794895239035908153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (3716748)
      previous := (1858374)
      next := (1858374)
      square := (13759582192456055950574578223190000000000000)
      linear := (-2229589484940335974009297832099676000000000000)
      constant := (93264564248480975504616033666432275951939278177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree165.table
  base := (68129730758921009740142242814563597354929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 108045000000000000000000000000000000000000000
      center := (1858374)
      previous := (929187)
      next := (929187)
      square := (6879791096228027975287289111595000000000000)
      linear := (-1117719823718564257402305076386400500000000000)
      constant := (46869581716734803932831515824667549775242660761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320105309721377714103/50000000000000000000)
  centralHi := (640210619442755428207/100000000000000000000)
  directionLo := (64215951472546362601/10000000000000000000)
  directionHi := (642159514725463626011/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree166.table
  base := (5547040689953092858699201756461574532211/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2442739945486057011703097550531818109000000000000)
      constant := (102817954965535055322507047531357639025711755660275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree166.table
  base := (69338008624404355932392107470459563438859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1224574691758771459699220864530646929500000000000)
      constant := (51670538768009590441145798105535361963715481198659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64215951472546362601/10000000000000000000)
  centralHi := (642159514725463626011/100000000000000000000)
  directionLo := (322051256579449343543/50000000000000000000)
  directionHi := (644102513158898687087/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree167.table
  base := (141112765468323834504874782671597929494567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2457456941872088147710069761907089054000000000000)
      constant := (104078501924225663639453204514749095199174979051967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree167.table
  base := (141112765468307874603105224825195230746063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2463904990976052886174663001753007429000000000000)
      constant := (104607946525071530822332513584748933237157734474663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322051256579449343543/50000000000000000000)
  centralHi := (644102513158898687087/100000000000000000000)
  directionLo := (32301983397416000513/5000000000000000000)
  directionHi := (646039667948320010261/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree168.table
  base := (2243276659009478647534013681402513457583/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (4589046)
      previous := (2294523)
      next := (2294523)
      square := (16988871890685538469586979234755000000000000)
      linear := (-2802918297344806444123630355195419500000000000)
      constant := (119440761159493843288195988320960205659522766816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree168.table
  base := (143569706176592946455505031337825603893929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9178092)
      previous := (4589046)
      next := (4589046)
      square := (33977743781371076939173958469510000000000000)
      linear := (-5620545574681548419389760259511839000000000000)
      constant := (240096498744243575414234386092399124049383945369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell058.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32301983397416000513/5000000000000000000)
  centralHi := (646039667948320010261/100000000000000000000)
  directionLo := (161992757875919776023/25000000000000000000)
  directionHi := (647971031503679104093/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree169.table
  base := (29209367874784744747719068056685954404067/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (4047538572)
      previous := (2023769286)
      next := (2023769286)
      square := (14984185007584644930175715685053910000000000000)
      linear := (-2486890934644150419724014184657630944000000000000)
      constant := (106622703220884609859029222986544361406191699307335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree169.table
  base := (73023419686955993192713778274907639943231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (2023769286)
      previous := (1011884643)
      next := (1011884643)
      square := (7492092503792322465087857842526955000000000000)
      linear := (-1246708102946536409863552773568217284500000000000)
      constant := (53582452899722338030856881141735596027579740481431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell058.Kernel169
