import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell095.Parameters
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch000_049
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch050_099
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch100_149
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch000_049
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch050_099
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree000.table
  base := (6092364657513597630099866321/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (796534728398670122118119250000000000000)
      linear := (-32900479758451294659549191000000000000)
      constant := (609236465751359763009986632100000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree000.table
  base := (6092364657513597630099866321/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (796534728398670122118119250000000000000)
      linear := (-32900479758451294659549191000000000000)
      constant := (609236465751359763009986632100000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree001.table
  base := (83004275826781003939378793448512008850509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-229929402987313409593376350330679250000000000)
      constant := (89109759272367242520697282103128371637369761308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree001.table
  base := (66341410303885490646559683294379562487319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-690532471098787736175483168666256500000000000)
      constant := (267080208092380326874093385306630768623046266355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24983669341130349117/50000000000000000000)
  directionHi := (9993467736452139647/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree002.table
  base := (9576438253174143956431503137945015444221/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-451034798601970906605177628987585500000000000)
      constant := (51606561181782109206890540371220372262478097260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree002.table
  base := (191215610587487023315975076583961371273303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-451530973359869244868747040770398000000000000)
      constant := (51523096276895124973994705128002940784613684509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24983669341130349117/50000000000000000000)
  centralHi := (9993467736452139647/20000000000000000000)
  directionLo := (70664488040142854927/100000000000000000000)
  directionHi := (4416530502508928433/6250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree003.table
  base := (29622489434101950906076043586221624003503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-224046731405542801205659635881497250000000000)
      constant := (10769316402966744505286549193658923950461186812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree003.table
  base := (118247179481943252778709084975805292511729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-672884456353475911012333025318710500000000000)
      constant := (32244006813708331647844153479036612586273252987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70664488040142854927/100000000000000000000)
  centralHi := (4416530502508928433/6250000000000000000)
  directionLo := (21636492329169310839/25000000000000000000)
  directionHi := (86545969316677243357/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree004.table
  base := (78995848612867763311403807914432401611721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-893245589831285900628780186301398000000000000)
      constant := (22120545505588555199260345820298258534468407363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree004.table
  base := (78822498039169151080934899065215939995787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-2682713818041247731467757029601069000000000000)
      constant := (66228384382703437707286824314401483264070182283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21636492329169310839/25000000000000000000)
  centralHi := (86545969316677243357/100000000000000000000)
  directionLo := (99934677364521396469/100000000000000000000)
  directionHi := (9993467736452139647/10000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree005.table
  base := (11282867502617607676268732187204449331757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-1114350985445943397640581464958304250000000000)
      constant := (16583570907330955080270631194324705831563613355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree005.table
  base := (28146138358453986742677768440941754955751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-1115591422340689243299504994415335500000000000)
      constant := (16554070815371682028971806549911585977544570906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99934677364521396469/100000000000000000000)
  centralHi := (9993467736452139647/10000000000000000000)
  directionLo := (111730365948289686319/100000000000000000000)
  directionHi := (1396629574353621079/1250000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree006.table
  base := (42547928111658682745796623635130685273511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-445152127020200298217460914538403500000000000)
      constant := (4499477435721169796054302626733030800387156911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree006.table
  base := (42459866469151091606852626354115363801733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-1336944905334295909443090978963648000000000000)
      constant := (13479469013033287868698846069625706542716195799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111730365948289686319/100000000000000000000)
  centralHi := (1396629574353621079/1250000000000000000)
  directionLo := (122394483576370702977/100000000000000000000)
  directionHi := (61197241788185351489/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree007.table
  base := (4166138311921600548429029598607764974447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-1556561776675258391664184022272116750000000000)
      constant := (11774210271022390063213094722963150263970369928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree007.table
  base := (33262603594227880813638801317971093572323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-4674895164983707726760030890535881500000000000)
      constant := (35288112383320390650472379090026640534383236707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122394483576370702977/100000000000000000000)
  centralHi := (61197241788185351489/50000000000000000000)
  directionLo := (13220115182899967471/10000000000000000000)
  directionHi := (132201151828999674711/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree008.table
  base := (26714579424896357774730031728979003211969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-1777667172289915888675985300929023000000000000)
      constant := (10862887422238488091730807464389564598459721707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree008.table
  base := (6665419195322234099995636905405351083411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-593217290440503080576754316020091000000000000)
      constant := (3618986949862822061018779380332678168832107244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13220115182899967471/10000000000000000000)
  centralHi := (132201151828999674711/100000000000000000000)
  directionLo := (28265795216057141971/20000000000000000000)
  directionHi := (4416530502508928433/3125000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree009.table
  base := (541436057872285106962043908285471578681/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-666257522634857795229262193195309750000000000)
      constant := (3494560270103470773182168420016136042038903240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree009.table
  base := (21613364804780697752983903036499376941733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-667001784771705302624616310869528500000000000)
      constant := (3494103338207051383444624277668278704217871933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28265795216057141971/20000000000000000000)
  centralHi := (4416530502508928433/3125000000000000000)
  directionLo := (9368876002923880919/6250000000000000000)
  directionHi := (29980403209356418941/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree010.table
  base := (17604550161836033537849554349924035658399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-2219877963519230882699587858242835500000000000)
      constant := (10488235285858575822152392551124636604439586997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree010.table
  base := (17566536578051462170998408479306649641791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-6667076511926167722052304751470694000000000000)
      constant := (31472809836114842496902744739534243436631814719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9368876002923880919/6250000000000000000)
  centralHi := (29980403209356418941/20000000000000000000)
  directionLo := (158010598852980311433/100000000000000000000)
  directionHi := (79005299426490155717/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree011.table
  base := (14250169968079260050652796577112054212359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-2440983359133888379711389136899741750000000000)
      constant := (10794552341713991334907118042310650361854820877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree011.table
  base := (14216648483114337129897891556552975252099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-2443712320302329240161020901705210500000000000)
      constant := (10801161129864907693308716161066504840288708097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158010598852980311433/100000000000000000000)
  centralHi := (79005299426490155717/50000000000000000000)
  directionLo := (165722914181670149637/100000000000000000000)
  directionHi := (82861457090835074819/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree012.table
  base := (5707406403649013304426201059594046023887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-887362918249515292241063471852216000000000000)
      constant := (3784830836456678648480992040215998492163043374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree012.table
  base := (5692440203527030831303557756134749815617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-2665065803295935906304606886253523000000000000)
      constant := (11365023477356822996204796853008992609595852502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165722914181670149637/100000000000000000000)
  centralHi := (82861457090835074819/50000000000000000000)
  directionLo := (173091938633354486713/100000000000000000000)
  directionHi := (86545969316677243357/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree013.table
  base := (8985274696827871824069729863808589463733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (193614)
      previous := (96807)
      next := (96807)
      square := (1264100613968689483801455249750000000000000)
      linear := (-17060320416350315820917110616648250000000000)
      constant := (71820675390912148615459468070312379916444271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree013.table
  base := (179167794828239878366403408591494255883/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3792301841906068451404365749250000000000000)
      linear := (-51238212182654601877778571671038500000000000)
      constant := (215720572693448407467647210619553363862948150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173091938633354486713/100000000000000000000)
  centralHi := (86545969316677243357/50000000000000000000)
  directionLo := (180159801717366190557/100000000000000000000)
  directionHi := (90079900858683095279/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree014.table
  base := (3442331485815670547802430690857631089023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-3104299545977860870746792972870460500000000000)
      constant := (13123534393355302410344619769532680930688471338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree014.table
  base := (6860472311102889211696446770448938573361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-3107772769283149238591778855350148000000000000)
      constant := (13142295193116831686384296696818554297191140283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180159801717366190557/100000000000000000000)
  centralHi := (90079900858683095279/50000000000000000000)
  directionLo := (93480330938958020031/50000000000000000000)
  directionHi := (186960661877916040063/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree015.table
  base := (2528579954089605909936292046804112678331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-1108468313864172789252864750509122250000000000)
      constant := (4765680928446591912829840116063898212923439462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree015.table
  base := (629425718739266141265964358236516180241/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-3329126252276755904735364839898460500000000000)
      constant := (14320187365729214297208543326845317261463415384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93480330938958020031/50000000000000000000)
  centralHi := (186960661877916040063/100000000000000000000)
  directionLo := (48380667642675334911/25000000000000000000)
  directionHi := (38704534114140267929/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree016.table
  base := (1730034773545007794972904952379685882677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-3546510337207175864770395530184273000000000000)
      constant := (15646768132623585129304286031589470785583238862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree016.table
  base := (1720270742608822932029735928862332183313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-10651439205811087712636852473340319000000000000)
      constant := (47023490913330527347272759274728338471366579234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48380667642675334911/25000000000000000000)
  centralHi := (38704534114140267929/20000000000000000000)
  directionLo := (199869354729042792939/100000000000000000000)
  directionHi := (9993467736452139647/5000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree017.table
  base := (2059497560024606828984466959725402093863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-3767615732821833361782196808841179250000000000)
      constant := (17163619874663186721643679027880550166217838189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree017.table
  base := (2042009202214641853768214806272859748943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-1257277739421323079007512269665028500000000000)
      constant := (5732046629739911413373634444027213340665253143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199869354729042792939/100000000000000000000)
  centralHi := (9993467736452139647/5000000000000000000)
  directionLo := (51505153804493006623/25000000000000000000)
  directionHi := (206020615217972026493/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree018.table
  base := (413935717988924245508779455317197897329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-1329573709478830286264666029166028500000000000)
      constant := (6280067660429823248122380067858880024688219858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree018.table
  base := (406124952724907803669098629903722877767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-1331062233752525301055374264514466000000000000)
      constant := (6292574904933263814754071700922917832990495134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51505153804493006623/25000000000000000000)
  centralHi := (206020615217972026493/100000000000000000000)
  directionLo := (105996732060214282391/50000000000000000000)
  directionHi := (211993464120428564783/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree019.table
  base := (-2575839387429265690133427336550284719/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-4209826524051148355805799366154991750000000000)
      constant := (20670409098684719791168563862068148609688504300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree019.table
  base := (-271502081810528811606235745298254871833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-12643620552753547707929126334275131500000000000)
      constant := (62139436875160019830873285846283662602079321703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105996732060214282391/50000000000000000000)
  centralHi := (211993464120428564783/100000000000000000000)
  directionLo := (217802579793645188887/100000000000000000000)
  directionHi := (27225322474205648611/12500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree020.table
  base := (-607927929979847620503157666113004711417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-4430931919665805852817600644811898000000000000)
      constant := (22649145777147595194246615961416900719767652698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree020.table
  base := (-614112859028738196102641910325906638493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-4435893667244789235453294762640023000000000000)
      constant := (22697312406376195270865174913627056723672523842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217802579793645188887/100000000000000000000)
  centralHi := (27225322474205648611/12500000000000000000)
  directionLo := (111730365948289686319/50000000000000000000)
  directionHi := (223460731896579372639/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree021.table
  base := (-1031430494141986215139397766152613272627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-1550679105093487783276467307822934750000000000)
      constant := (8257381373517368607150148013508919761940247146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree021.table
  base := (-1036914606754770526209058715849544931407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-4657247150238395901596880747188335500000000000)
      constant := (24825958429063121337646050601022284970273696758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111730365948289686319/50000000000000000000)
  centralHi := (223460731896579372639/100000000000000000000)
  directionLo := (114489555893477323019/50000000000000000000)
  directionHi := (228979111786954646039/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree022.table
  base := (-562397006296758466876428087923602446019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-4873142710895120846841203202125710500000000000)
      constant := (27035814041917741596894181469570872984601830715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree022.table
  base := (-705422340457878303613453112852375662267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-14635801899696007703221400195209944000000000000)
      constant := (81286487990768521075077944703766666358036045588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114489555893477323019/50000000000000000000)
  centralHi := (228979111786954646039/100000000000000000000)
  directionLo := (234367592831710456181/100000000000000000000)
  directionHi := (117183796415855228091/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree023.table
  base := (-347450637816786792939205071234758954989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (61854)
      previous := (30927)
      next := (30927)
      square := (403843107298125751913886459750000000000000)
      linear := (-9629958613440034676470707903180750000000000)
      constant := (55646749798836445887061242164314795535705770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree023.table
  base := (-3483075210647309018648598837266697433957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (61854)
      previous := (30927)
      next := (30927)
      square := (403843107298125751913886459750000000000000)
      linear := (-9640745021220433334374390768024500000000000)
      constant := (55771082641919612764495973404612253150983801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234367592831710456181/100000000000000000000)
  centralHi := (117183796415855228091/50000000000000000000)
  directionLo := (119817468994214450373/50000000000000000000)
  directionHi := (239634937988428900747/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree024.table
  base := (-811987645804831976418015900242824359507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-1771784500708145280288268586479841000000000000)
      constant := (10657847485529402512940426015633040297178573465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree024.table
  base := (-4067490376627738841769387678936391783719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-5321307599219215900027638700833273000000000000)
      constant := (32045629692519064364343199835393649914431213043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119817468994214450373/50000000000000000000)
  centralHi := (239634937988428900747/100000000000000000000)
  directionLo := (122394483576370702977/50000000000000000000)
  directionHi := (48957793430548281191/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree025.table
  base := (-2288154969978021968965763957001614292027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-5536458897739093337876607038096429250000000000)
      constant := (34642895983587571505533476172489228607508465038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree025.table
  base := (-1145738650924994329321825672850026690419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-16627983246638467698513674056144756500000000000)
      constant := (104164578007119323927738846461763011654844635316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122394483576370702977/50000000000000000000)
  centralHi := (48957793430548281191/20000000000000000000)
  directionLo := (124918346705651745587/50000000000000000000)
  directionHi := (9993467736452139647/4000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree026.table
  base := (-5030400945599742360152817416149548377483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (193614)
      previous := (96807)
      next := (96807)
      square := (1264100613968689483801455249750000000000000)
      linear := (-34068427771323969437209516667179500000000000)
      constant := (221558419880916171921450849321886885474934479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree026.table
  base := (-629529735221673321017564850064887870801/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (421366871322896494600485083250000000000000)
      linear := (-11368865020131024126853669960414000000000000)
      constant := (74021254271270109147276586897398769530770168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124918346705651745587/50000000000000000000)
  centralHi := (9993467736452139647/4000000000000000000)
  directionLo := (12739221749157344381/5000000000000000000)
  directionHi := (254784434983146887621/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree027.table
  base := (-2713968271082512170838935587819726292757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-1992889896322802777300069865136747250000000000)
      constant := (13457812614610214486515551723401545744714962886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree027.table
  base := (-5433056386331172146375503485030440507031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-1995122682733345299486132218159403500000000000)
      constant := (13488615445529484756978841109124816994480921569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12739221749157344381/5000000000000000000)
  centralHi := (254784434983146887621/100000000000000000000)
  directionLo := (259637907950031730069/100000000000000000000)
  directionHi := (25963790795003173007/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree028.table
  base := (-2886876192885599741193449762610212184577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-6199775084583065828912010874067148000000000000)
      constant := (43431793697976835527381189025032616147919789738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree028.table
  base := (-1155647418398897507554730252051341729857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-18620164593580927693805947917079569000000000000)
      constant := (130594327969386952642103408335723291910407445435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259637907950031730069/100000000000000000000)
  centralHi := (25963790795003173007/10000000000000000000)
  directionLo := (13220115182899967471/5000000000000000000)
  directionHi := (264402303657999349421/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree029.table
  base := (-3035966509518333964374600456469824527953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-6420880480197723325923812152724054250000000000)
      constant := (46617345035729526483745289848221221140196343082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree029.table
  base := (-759482047067726509132747585922535477551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-6428075014187249230745568623574835500000000000)
      constant := (46724471578406213675024089351416318207265113176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13220115182899967471/5000000000000000000)
  centralHi := (264402303657999349421/100000000000000000000)
  directionLo := (269082353777880875817/100000000000000000000)
  directionHi := (134541176888940437909/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree030.table
  base := (-1265185736058072555905390099535828885659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-2213995291937460274311871143793653500000000000)
      constant := (16643055497606060494917215325210939465215998705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree030.table
  base := (-6329356875904707875760160766965820787369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-6649428497180855896889154608123148000000000000)
      constant := (50044009777135389897691037260941671592365272093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269082353777880875817/100000000000000000000)
  centralHi := (134541176888940437909/50000000000000000000)
  directionLo := (273682385347746464597/100000000000000000000)
  directionHi := (136841192673873232299/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree031.table
  base := (-6538653875377487903474723764949176700161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-6863091271427038319947414710037866750000000000)
      constant := (53366476390031599317188673998327097984924219317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree031.table
  base := (-3270823038308826813604257380146403587369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-20612345940523387689098221778014381500000000000)
      constant := (160467832368116518288791383362516645118191232558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273682385347746464597/100000000000000000000)
  centralHi := (136841192673873232299/50000000000000000000)
  directionLo := (139103183810274571861/50000000000000000000)
  directionHi := (278206367620549143723/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree032.table
  base := (-33562852981121366894892932812608047797/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-7084196667041695816959215988694773000000000000)
      constant := (56928614413749189295342995897734102751340241800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree032.table
  base := (-6715179535838736831040914893092702326369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-7092135463168069229176326577219773000000000000)
      constant := (57059616027320091728005245498550093957960855093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139103183810274571861/50000000000000000000)
  centralHi := (278206367620549143723/100000000000000000000)
  directionLo := (28265795216057141971/10000000000000000000)
  directionHi := (282657952160571419711/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree033.table
  base := (-6849758595479102700376038347465561677139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-2435100687552117771323672422450559750000000000)
      constant := (20205007589357132340294270435656507953314596261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree033.table
  base := (-3426015571666686735962678138388719727143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-7313488946161675895319912561768085500000000000)
      constant := (60754469267522392929579480101209293624792131942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28265795216057141971/10000000000000000000)
  centralHi := (282657952160571419711/100000000000000000000)
  directionLo := (287040507341029530181/100000000000000000000)
  directionHi := (143520253670514765091/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree034.table
  base := (-6951974739298845641420406964974226124683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-7526407458271010810982818546008585500000000000)
      constant := (64425230256224351549878156437969011349431645351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree034.table
  base := (-6953952451639885028347038002419588874407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-22604527287465847684390495638949194000000000000)
      constant := (193720102215000922796476997230980632390352258137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287040507341029530181/100000000000000000000)
  centralHi := (143520253670514765091/50000000000000000000)
  directionLo := (291357148169704897491/100000000000000000000)
  directionHi := (72839287042426224373/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree035.table
  base := (-1755175784997135039940676200832166465281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-7747512853885668307994619824665491750000000000)
      constant := (68358838834835504786973156815158419290986459828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree035.table
  base := (-3511211389711793288498606359948922922173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-2585398637382963075869028176954903500000000000)
      constant := (22838637894016614078743326130482476589919623254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291357148169704897491/100000000000000000000)
  centralHi := (72839287042426224373/25000000000000000000)
  directionLo := (2956107621934139261/1000000000000000000)
  directionHi := (295610762193413926101/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree036.table
  base := (-882149687859690177402490966456470216397/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-2656206083166775268335473701107466000000000000)
      constant := (24138504085458137684408867565150461224471134424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree036.table
  base := (-352934576248330376296375254392603856359/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-2659183131714165297916890171804341000000000000)
      constant := (24193924335434511629388249385416587452752980820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2956107621934139261/1000000000000000000)
  centralHi := (295610762193413926101/100000000000000000000)
  directionLo := (299804032093564189409/100000000000000000000)
  directionHi := (29980403209356418941/10000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree037.table
  base := (-7062516897600859060645204487187859979423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-8189723645114983302018222381979304250000000000)
      constant := (76594966475187741765752762392132759100876313131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree037.table
  base := (-7063813901916243489839081445322517419371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-24596708634408307679682769499884006500000000000)
      constant := (230311987098886619786640834367312801487967319061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299804032093564189409/100000000000000000000)
  centralHi := (29980403209356418941/10000000000000000000)
  directionLo := (303939455475176195117/100000000000000000000)
  directionHi := (151969727737588097559/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree038.table
  base := (-879694496916750611617529850603862842651/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-8410829040729640799030023660636210500000000000)
      constant := (80896961543146281223048772258392785610849790776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree038.table
  base := (-7038681120298677778358056224583778156511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-8420256361129709226037842484509648000000000000)
      constant := (81082342736823204916184915520931596572089280267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303939455475176195117/100000000000000000000)
  centralHi := (151969727737588097559/50000000000000000000)
  directionLo := (154009681132010625839/50000000000000000000)
  directionHi := (308019362264021251679/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree039.table
  base := (-55864563956583808914624648763365056723/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (421366871322896494600485083250000000000000)
      linear := (-17025511708765874351167307572570250000000000)
      constant := (168286577442907542651873008885390555936691625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree039.table
  base := (-6984045876454558953977002418684101490591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (193614)
      previous := (96807)
      next := (96807)
      square := (1264100613968689483801455249750000000000000)
      linear := (-51133786059901277468529162538804500000000000)
      constant := (506015457056034786293919910043060549684432083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154009681132010625839/50000000000000000000)
  centralHi := (308019362264021251679/100000000000000000000)
  directionLo := (312045930056012916673/100000000000000000000)
  directionHi := (156022965028006458337/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree040.table
  base := (-6899698883960657692299587956149758336279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-8853039831958955793053626217950023000000000000)
      constant := (89867794907933962793169341919696561364934963363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree040.table
  base := (-1380108776230114193292131752674924478721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-26588889981350767674975043360818819000000000000)
      constant := (270219901151102414687892521184989543450503874555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312045930056012916673/100000000000000000000)
  centralHi := (156022965028006458337/50000000000000000000)
  directionLo := (316021197705960622867/100000000000000000000)
  directionHi := (79005299426490155717/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree041.table
  base := (-6787980457476264069206320026638295539809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-9074145227573613290065427496606929250000000000)
      constant := (94536317330658629977975935884575427494774106773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree041.table
  base := (-6788712041696129516212233932398671155493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-9084316810110529224468600438154585500000000000)
      constant := (94752263160364875733964800538165458918833310921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316021197705960622867/100000000000000000000)
  centralHi := (79005299426490155717/25000000000000000000)
  directionLo := (39993384674549926967/12500000000000000000)
  directionHi := (319947077396399415737/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree042.table
  base := (-831046350217139407454925625007204561523/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-3098416874396090262359076258421278500000000000)
      constant := (33108913280676866866348671059612654396212258216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree042.table
  base := (-6649003818140975193887592486009123911783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-9305670293104135890612186422702898000000000000)
      constant := (99553378953116370822038670384130564064488064051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39993384674549926967/12500000000000000000)
  centralHi := (319947077396399415737/100000000000000000000)
  directionLo := (40478170673657035999/12500000000000000000)
  directionHi := (323825365389256287993/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree043.table
  base := (-1620313693613040757226684845858129887727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-9516356018802928284089030053920741750000000000)
      constant := (104238959222057760666068700035610612544825321676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree043.table
  base := (-6481802192779070612049726757387198029791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-28581071328293227670267317221753631500000000000)
      constant := (313429635134865307516825653100466883636697893281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40478170673657035999/12500000000000000000)
  centralHi := (323825365389256287993/100000000000000000000)
  directionLo := (65531550326380373379/20000000000000000000)
  directionHi := (20478609476993866681/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree044.table
  base := (-6286957484897396283956584847664366223857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-9737461414417585781100831332577648000000000000)
      constant := (109272888275456962126233751829972601610662881029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree044.table
  base := (-3143715311954925968403837868270680508699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-3249459086363783074299786130599841000000000000)
      constant := (36507224894464929035538499967334469783683601402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65531550326380373379/20000000000000000000)
  centralHi := (20478609476993866681/6250000000000000000)
  directionLo := (165722914181670149637/50000000000000000000)
  directionHi := (13257833134533611971/4000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree045.table
  base := (-1516438392425527489576778250835542548929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-3319522270010747759370877537078184750000000000)
      constant := (38142817781286772730162264793816376837645293884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree045.table
  base := (-6066162297149727673293984707060567154161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-3323243580694985296347648125449278500000000000)
      constant := (38229564866411182338252484315659833392100852439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165722914181670149637/50000000000000000000)
  centralHi := (13257833134533611971/4000000000000000000)
  directionLo := (335191097844869058957/100000000000000000000)
  directionHi := (167595548922434529479/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree046.table
  base := (-2908937514297817769959867734938428414753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (61854)
      previous := (30927)
      next := (30927)
      square := (403843107298125751913886459750000000000000)
      linear := (-19243236683642534546549024366524500000000000)
      constant := (226286563713127453621478474876142402337440458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree046.table
  base := (-2909113969446117727462196535794599570653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (185562)
      previous := (92781)
      next := (92781)
      square := (1211529321894377255741659379250000000000000)
      linear := (-57794428497609995587069170288636000000000000)
      constant := (680401944674633967426121409905915703106073574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335191097844869058957/100000000000000000000)
  centralHi := (167595548922434529479/50000000000000000000)
  directionLo := (10590468103802242481/3125000000000000000)
  directionHi := (338894979321671759393/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree047.table
  base := (-5543517843677048133304539490137216535139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-10400777601261558272136235168548366750000000000)
      constant := (125104252293622358211804789385264064387063614783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree047.table
  base := (-5543822415390082245202037852865027009467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-10412437708072169221330116345444460500000000000)
      constant := (125388167354861940065028935042384977629729922199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10590468103802242481/3125000000000000000)
  centralHi := (338894979321671759393/100000000000000000000)
  directionLo := (34255881530683760187/10000000000000000000)
  directionHi := (342558815306837601871/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree048.table
  base := (-1310711892765623486318722899688171142297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-3540627665625405256382678815735091000000000000)
      constant := (43541463069782368389169619188038704246830023612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree048.table
  base := (-1048622061239875628329136252256088828299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-10633791191065775887473702329992773000000000000)
      constant := (130920523790207311044941207652791155039918616515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34255881530683760187/10000000000000000000)
  centralHi := (342558815306837601871/100000000000000000000)
  directionLo := (173091938633354486713/50000000000000000000)
  directionHi := (346183877266708973427/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree049.table
  base := (-245800203222273542066025713035162584731/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-10842988392490873266159837725862179250000000000)
      constant := (136265965442238506624856377711760447434185332140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree049.table
  base := (-2458115305695973081235822357733231573859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-32565434022178147660851864943623256500000000000)
      constant := (409723724810280918140764663173561723209427767738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173091938633354486713/50000000000000000000)
  centralHi := (346183877266708973427/100000000000000000000)
  directionLo := (87442842693956221911/25000000000000000000)
  directionHi := (69954274155164977529/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree050.table
  base := (-4563105465337941608884263466133288367871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-11064093788105530763171639004519085500000000000)
      constant := (142028949306388629628366813523072377878621894187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree050.table
  base := (-2281650363583236064698479191964862250267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-11076498157052989219760874299089398000000000000)
      constant := (142350289308508248937528002615289249224783279598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87442842693956221911/25000000000000000000)
  centralHi := (69954274155164977529/20000000000000000000)
  directionLo := (176661220100357137319/50000000000000000000)
  directionHi := (353322440200714274639/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree051.table
  base := (-836850314767566774266188243557206172651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-3761733061240062753394480094391997250000000000)
      constant := (49304438011703936565223618335503386625106639745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree051.table
  base := (-4184419803564770783982733519422299897521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-11297851640046595885904460283637710500000000000)
      constant := (148247640313112474877629637603775315619335175237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176661220100357137319/50000000000000000000)
  centralHi := (353322440200714274639/100000000000000000000)
  directionLo := (178419086482062689693/50000000000000000000)
  directionHi := (356838172964125379387/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree052.table
  base := (-151181067843772219992485729204755185039/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (193614)
      previous := (96807)
      next := (96807)
      square := (1264100613968689483801455249750000000000000)
      linear := (-68084642481271276669794328768242000000000000)
      constant := (910763532646425587208591897850113463033577675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree052.table
  base := (-1889835790163543065841393855567035716849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3792301841906068451404365749250000000000000)
      linear := (-204482931178228447669491945589101000000000000)
      constant := (2738460452508699962205296966587667685904163822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178419086482062689693/50000000000000000000)
  centralHi := (356838172964125379387/100000000000000000000)
  directionLo := (72063920686946476223/20000000000000000000)
  directionHi := (90079900858683095279/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree053.table
  base := (-1674501024855924724967409948958118308633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-11727409974949503254207042840489804250000000000)
      constant := (160046099152015795431937689796817063051476907002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree053.table
  base := (-418640847749331460852222334182439888707/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-3913519535344603072730544084244778500000000000)
      constant := (53469055291535661821697644598768466188327643944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72063920686946476223/20000000000000000000)
  centralHi := (90079900858683095279/25000000000000000000)
  directionLo := (181883858240877544777/50000000000000000000)
  directionHi := (72753543296351017911/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree054.table
  base := (-2892737795721893118652492712723794318627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-3982838456854720250406281373048903500000000000)
      constant := (55431494768017437118194235620785597970370427573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree054.table
  base := (-2892845140761813577786353314618966657549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-3987304029675805294778406079094216000000000000)
      constant := (55556435147536472481846116447550085636848461851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181883858240877544777/50000000000000000000)
  centralHi := (72753543296351017911/20000000000000000000)
  directionLo := (91795862682278027233/25000000000000000000)
  directionHi := (367183450729112108933/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree055.table
  base := (-602696188774041783112173093969628309591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-12169620766178818248230645397803616750000000000)
      constant := (172664178843018390936972319548597691012368560108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree055.table
  base := (-1205438552466661297462944803381248751479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-36549796716063067651436412665492881500000000000)
      constant := (519159031994832144208041359917625857552892466578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91795862682278027233/25000000000000000000)
  centralHi := (367183450729112108933/100000000000000000000)
  directionLo := (370567701539578386947/100000000000000000000)
  directionHi := (92641925384894596737/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree056.table
  base := (-237898232346974563795704466054254003343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-12390726161793475745242446676460523000000000000)
      constant := (179155171254706831625624348172118645308331178968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree056.table
  base := (-951632640925212143783826926021371489293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-12404619055014629216622390206379273000000000000)
      constant := (179558270114194133256451952069944243204914299042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370567701539578386947/100000000000000000000)
  centralHi := (92641925384894596737/25000000000000000000)
  directionLo := (93480330938958020031/25000000000000000000)
  directionHi := (2991370590046656641/800000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree057.table
  base := (-684988686293507891763296858644994951123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-4203943852469377747418082651705809750000000000)
      constant := (61922483937504746613529312698382777620561805354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree057.table
  base := (-1370045656554940608684573952239450001687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-12625972538008235882765976190927585500000000000)
      constant := (186185074139063501233599647452816095509947541539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93480330938958020031/25000000000000000000)
  centralHi := (2991370590046656641/800000000000000000)
  directionLo := (377245134222167985001/100000000000000000000)
  directionHi := (188622567111083992501/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree058.table
  base := (-811189931991707090781268733167662901627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-12832936953022790739266049233774335500000000000)
      constant := (192501012299917832406577182587388135275544933719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree058.table
  base := (-162249724209287020832815687390615648553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-38541978063005527646728686526427694000000000000)
      constant := (578800243764980079177277680381699232043167096115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377245134222167985001/100000000000000000000)
  centralHi := (188622567111083992501/50000000000000000000)
  directionLo := (95134978526988591029/25000000000000000000)
  directionHi := (380539914107954364117/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree059.table
  base := (-113424708097680623989214714050308782537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-13054042348637448236277850512431241750000000000)
      constant := (199355845776037059070308994350056693903131957978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree059.table
  base := (-226899843570337675278958569383096282167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-13068679503995449215053148160024210500000000000)
      constant := (199803284577683279697119623658031301646583964099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95134978526988591029/25000000000000000000)
  centralHi := (380539914107954364117/100000000000000000000)
  directionLo := (383806411051557385493/100000000000000000000)
  directionHi := (191903205525778692747/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree060.table
  base := (383022313448230682095819368450414067523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-4425049248084035244429883930362716000000000000)
      constant := (68777315459197083002456983903192717343050623723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree060.table
  base := (191489498600181140410116948099079088793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-13290032986989055881196734144572523000000000000)
      constant := (206794678292848129372396868613059664617703097958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383806411051557385493/100000000000000000000)
  centralHi := (191903205525778692747/50000000000000000000)
  directionLo := (387045341141402679289/100000000000000000000)
  directionHi := (38704534114140267929/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree061.table
  base := (254601697416999742707999252906949656253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-13496253139866763230301453069745054250000000000)
      constant := (213429309151602899503340806128559757810561593436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree061.table
  base := (1018369592091420397027217138265126871317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-40534159409947987642020960387362506500000000000)
      constant := (641722772469737346668799866666818640873053500053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387045341141402679289/100000000000000000000)
  centralHi := (38704534114140267929/10000000000000000000)
  directionLo := (195128695374522326917/50000000000000000000)
  directionHi := (78051478149808930767/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree062.table
  base := (419822103086361972305571548199164233239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-13717358535481420727313254348401960500000000000)
      constant := (220647929914073429648211473981373710748139598068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree062.table
  base := (104953529857925413445174829873082641533/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-4577579984325423071161302037889716000000000000)
      constant := (73714006007184132286341440676594049254771067728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195128695374522326917/50000000000000000000)
  centralHi := (78051478149808930767/20000000000000000000)
  directionLo := (393443218227535687243/100000000000000000000)
  directionHi := (98360804556883921811/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree063.table
  base := (1182827001694684975494232932638500779059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-4646154643698692741441685209019622250000000000)
      constant := (75995935043533081106846892516212432724109807318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree063.table
  base := (2365626594222875226532542023568346428047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-4651364478656625293209164032739153500000000000)
      constant := (76165985461689333283564393190548426895263829847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393443218227535687243/100000000000000000000)
  centralHi := (98360804556883921811/25000000000000000000)
  directionLo := (39660345548699902413/10000000000000000000)
  directionHi := (396603455486999024131/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree064.table
  base := (1923432769197144613581257996728176057/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-14159569326710735721336856905715773000000000000)
      constant := (235448931815521925949032873297340551204824913600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree064.table
  base := (3077468911626742939928191458730632005881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-42526340756890447637313234248297319000000000000)
      constant := (707926208866578414121667244660567211087619905529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39660345548699902413/10000000000000000000)
  centralHi := (396603455486999024131/100000000000000000000)
  directionLo := (399738709458085585879/100000000000000000000)
  directionHi := (9993467736452139647/2500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree065.table
  base := (381479429060227470360691956328654537669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (193614)
      previous := (96807)
      next := (96807)
      square := (1264100613968689483801455249750000000000000)
      linear := (-85092749836244930286086734818773250000000000)
      constant := (1438055073649320699964845785313375708450307030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree065.table
  base := (762954822882907554671701151943756994661/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (193614)
      previous := (96807)
      next := (96807)
      square := (1264100613968689483801455249750000000000000)
      linear := (-85188168058917687644465467853929500000000000)
      constant := (1441268374168493268588383192905134180502635035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399738709458085585879/100000000000000000000)
  centralHi := (9993467736452139647/2500000000000000000)
  directionLo := (201424781726457078047/50000000000000000000)
  directionHi := (80569912690582831219/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree066.table
  base := (2288775819680665099301593098890097533959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-4867260039313350238453486487676528500000000000)
      constant := (83578309964572651630512608523240732125516937118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree066.table
  base := (183101373401030204208022851902449161851/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-14618153884950695878058250051862398000000000000)
      constant := (251294811111812342882303083409950035438898093825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201424781726457078047/50000000000000000000)
  centralHi := (80569912690582831219/20000000000000000000)
  directionLo := (5074207230401723909/1250000000000000000)
  directionHi := (405936578432137912721/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree067.table
  base := (5365757766664503049459820860623384337027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-14822885513554708212372260741686491750000000000)
      constant := (258559797356740069727196223464799749510281152481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree067.table
  base := (33535893305077766224727754587457652707/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-44518522103832907632605508109232131500000000000)
      constant := (777410306416267694255533055031514587474158250080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5074207230401723909/1250000000000000000)
  centralHi := (405936578432137912721/100000000000000000000)
  directionLo := (409000294185932097973/100000000000000000000)
  directionHi := (204500147092966048987/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree068.table
  base := (6179407004062449440130913334140852818349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-15043990909169365709384062020343398000000000000)
      constant := (266505908315506423441539170145081996273439656847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree068.table
  base := (617939428396644521878164763982669174761/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-15060860850937909210345422020959023000000000000)
      constant := (267100226810202245397395797972924627206784244830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409000294185932097973/100000000000000000000)
  centralHi := (204500147092966048987/50000000000000000000)
  directionLo := (82408246087188810597/20000000000000000000)
  directionHi := (206020615217972026493/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree069.table
  base := (7018494563230183156874508958332176254467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (134614369099375250637962153250000000000000)
      linear := (-9618838251281678138875780276622750000000000)
      constant := (173014027401243786866466560897853083099504923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree069.table
  base := (280739346439534133191645641766359053487/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (61854)
      previous := (30927)
      next := (30927)
      square := (403843107298125751913886459750000000000000)
      linear := (-28888873977186230390338389424399500000000000)
      constant := (520198835264656757380413081231872069752947725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82408246087188810597/20000000000000000000)
  centralHi := (206020615217972026493/50000000000000000000)
  directionLo := (207529943932288054579/50000000000000000000)
  directionHi := (415059887864576109159/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree070.table
  base := (985377049915613766417784777226445474699/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-15486201700398680703407664577657210500000000000)
      constant := (282761855782703496776312782443217274063955567176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree070.table
  base := (788300705710672323836457402752651025633/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-46510703450775367627897781970166944000000000000)
      constant := (850174916598812379030651206305613204765835424970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207529943932288054579/50000000000000000000)
  centralHi := (415059887864576109159/100000000000000000000)
  directionLo := (418056749077373753117/100000000000000000000)
  directionHi := (209028374538686876559/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree071.table
  base := (8772969095557470597482193413798851243131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-15707307096013338200419465856314116750000000000)
      constant := (291071690289902141482495769055159353448398963593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree071.table
  base := (2193240272942436691428574892590643624411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-5241640433306243069592059991534653500000000000)
      constant := (97239863645776737952118687023322668178913871244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418056749077373753117/100000000000000000000)
  centralHi := (209028374538686876559/50000000000000000000)
  directionLo := (84206455900751454597/20000000000000000000)
  directionHi := (210516139751878636493/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree072.table
  base := (605521860355251188579399458442702737407/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-5309470830542665232477089044990341000000000000)
      constant := (99834254744423521923598925931960904078830771312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree072.table
  base := (4844171454967121810419492376591644062961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-5315424927637445291639921986384091000000000000)
      constant := (100056346434150180369689355460982266141745552722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84206455900751454597/20000000000000000000)
  centralHi := (210516139751878636493/50000000000000000000)
  directionLo := (84797385648171425913/20000000000000000000)
  directionHi := (211993464120428564783/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree073.table
  base := (10629155971635859047318788234080374534673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-16149517887242653194443068413627929250000000000)
      constant := (308055076958911431075830094440033980464760402619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree073.table
  base := (10629150100385875778656327870498915268259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-48502884797717827623190055831101756500000000000)
      constant := (926219949944810567001035808429469958871328605731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84797385648171425913/20000000000000000000)
  centralHi := (211993464120428564783/50000000000000000000)
  directionLo := (426921128844784958193/100000000000000000000)
  directionHi := (213460564422392479097/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree074.table
  base := (90588950421384860081234983800411189541/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-16370623282857310691454869692284835500000000000)
      constant := (316728627914467168560633027381055257799113497344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree074.table
  base := (11595380626754395017787173712762489508697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-16388981748899549207206937928248898000000000000)
      constant := (317432422428628547846469116785931443098701061491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426921128844784958193/100000000000000000000)
  centralHi := (213460564422392479097/50000000000000000000)
  directionLo := (429835300073287635447/100000000000000000000)
  directionHi := (53729412509160954431/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree075.table
  base := (6293518536462978129262544892988189579157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-5530576226157322729488890323647247250000000000)
      constant := (108507805544451712639344275435827161968444929914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree075.table
  base := (3146758192312707313858878010141014956851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-16610335231893155873350523912797210500000000000)
      constant := (326246356182273055967917469977030701756639235012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429835300073287635447/100000000000000000000)
  centralHi := (53729412509160954431/12500000000000000000)
  directionLo := (216364923291693108391/50000000000000000000)
  directionHi := (432729846583386216783/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree076.table
  base := (6802054379549593819694376368087646464843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-16812834074086625685478472249598648000000000000)
      constant := (334439442721450292040485925023388485714620574258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree076.table
  base := (425128283608130473594885774506195601487/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-50495066144660287618482329692036569000000000000)
      constant := (1005545352558984956674440760617495721174939314656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216364923291693108391/50000000000000000000)
  centralHi := (432729846583386216783/100000000000000000000)
  directionLo := (17424206383491615111/4000000000000000000)
  directionHi := (27225322474205648611/6250000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree077.table
  base := (7323299735584310646779740940406011544723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-17033939469701283182490273528255554250000000000)
      constant := (343476705845835375632232490570850711114596185538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree077.table
  base := (14646596318782164505846108296234585097713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-17053042197880369205637695881893835500000000000)
      constant := (344238706111816464882231411471403255895711919739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17424206383491615111/4000000000000000000)
  centralHi := (27225322474205648611/6250000000000000000)
  directionLo := (219230808734799215729/50000000000000000000)
  directionHi := (438461617469598431459/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree078.table
  base := (15714508160627293911976742047681868001513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (421366871322896494600485083250000000000000)
      linear := (-34033619063739527967459713623101500000000000)
      constant := (695532950148516125469216095138219614422800377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree078.table
  base := (1964313182916427217316847075299167108631/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (193614)
      previous := (96807)
      next := (96807)
      square := (1264100613968689483801455249750000000000000)
      linear := (-102215359058425892732433620511492000000000000)
      constant := (2091225572076390103452887117262514850611179176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219230808734799215729/50000000000000000000)
  centralHi := (438461617469598431459/100000000000000000000)
  directionLo := (441299586368539677909/100000000000000000000)
  directionHi := (44129958636853967791/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree079.table
  base := (16807833941817628776878746865964999223243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-17476150260930598176513876085569366750000000000)
      constant := (361914942122301172934032269626055395460108942329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree079.table
  base := (16807831634293045997556050632157432734961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-52487247491602747613774603552971381500000000000)
      constant := (1088151091976942187179027110582321827201694235249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441299586368539677909/100000000000000000000)
  centralHi := (44129958636853967791/10000000000000000000)
  directionLo := (444119420723786809947/100000000000000000000)
  directionHi := (111029855180946702487/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree080.table
  base := (17926576066646477627660105621537752134177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-17697255656545255673525677364226273000000000000)
      constant := (371315914836205040952712471138084754735642673931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree080.table
  base := (8963287046442898710704482054826197196959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-5905700882287063068022817945179591000000000000)
      constant := (124046144282628507172544869981180563711210663118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444119420723786809947/100000000000000000000)
  centralHi := (111029855180946702487/25000000000000000000)
  directionLo := (111730365948289686319/25000000000000000000)
  directionHi := (446921463793158745277/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree081.table
  base := (19070733903225741300227435281317589803051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-5972787017386637723512492880961059750000000000)
      constant := (126946041232511665269608609053847862228795062451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree081.table
  base := (2383841526902078303180208970459719582311/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-5979485376618265290070679940029028500000000000)
      constant := (127227109360098106117491421069465492529275485688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111730365948289686319/25000000000000000000)
  centralHi := (446921463793158745277/100000000000000000000)
  directionLo := (224853024070173142057/50000000000000000000)
  directionHi := (89941209628069256823/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree082.table
  base := (5060076729457281110681492361504059877411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-18139466447774570667549279921540085500000000000)
      constant := (390481568563144043910118833783843578703955049732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree082.table
  base := (20240305474421865974218536708394974308853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-54479428838545207609066877413906194000000000000)
      constant := (1174037148644702110422869157606937239258671903477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224853024070173142057/50000000000000000000)
  centralHi := (89941209628069256823/20000000000000000000)
  directionLo := (226236748047811187079/50000000000000000000)
  directionHi := (452473496095622374159/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree083.table
  base := (5358823664912548698321039537452887351677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-18360571843389228164561081200196991750000000000)
      constant := (400246249312124547704660755689501332196464805724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree083.table
  base := (10717646712792092701984533689966323903989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-18381163095842009202499211789183710500000000000)
      constant := (401131597132376514047065740776384496658793123534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226236748047811187079/50000000000000000000)
  centralHi := (452473496095622374159/100000000000000000000)
  directionLo := (455224120191343707937/100000000000000000000)
  directionHi := (227612060095671853969/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree084.table
  base := (11327848373963421956815437135108712669347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-6193892413001295220524294159617966000000000000)
      constant := (136710721947451655807660653923628236417704582294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree084.table
  base := (4531139138598781777072473958596111453567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-18602516578835615868642797773732023000000000000)
      constant := (411038970731955287884348294171070571400905150505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455224120191343707937/100000000000000000000)
  centralHi := (227612060095671853969/50000000000000000000)
  directionLo := (114489555893477323019/25000000000000000000)
  directionHi := (457958223573909292077/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree085.table
  base := (746922276908273884292959658673833468223/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-18802782634618543158584683757510804250000000000)
      constant := (420139318067582745008945757032469706006627524608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree085.table
  base := (11950755979695161408190901968142455047351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-56471610185487667604359151274841006500000000000)
      constant := (1263203510785640249447807131456297009132638081518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114489555893477323019/25000000000000000000)
  centralHi := (457958223573909292077/100000000000000000000)
  directionLo := (92135220078742620811/20000000000000000000)
  directionHi := (57584512549214138007/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree086.table
  base := (5034548545489918756150626192088917548689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-19023888030233200655596485036167710500000000000)
      constant := (430267705914960093687144539208483284485305179335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree086.table
  base := (5034548391375046420188545988692832034843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-19045223544822829200929969742828648000000000000)
      constant := (431218195650299800222472801053386661776204985645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92135220078742620811/20000000000000000000)
  centralHi := (57584512549214138007/12500000000000000000)
  directionLo := (463378036174510736851/100000000000000000000)
  directionHi := (115844509043627684213/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree087.table
  base := (13234693058842779740644813701700934389529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-6414997808615952717536095438274872250000000000)
      constant := (146839109774320792994393153404247058603529064258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree087.table
  base := (13234692729619427565665136125886951422483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-19266577027816435867073555727376960500000000000)
      constant := (441490046836544297047425613104378810033478416098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463378036174510736851/100000000000000000000)
  centralHi := (115844509043627684213/25000000000000000000)
  directionLo := (466064308163512910863/100000000000000000000)
  directionHi := (29129019260219556929/6250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree088.table
  base := (27791442838039154746315710078709788636417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-19466098821462515649620087593481523000000000000)
      constant := (450888188239629693212284873470282625441652948651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree088.table
  base := (3473930284434817917656134628554491469809/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-58463791532430127599651425135775819000000000000)
      constant := (1355650171308158270812104101563188503616252397448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466064308163512910863/100000000000000000000)
  centralHi := (29129019260219556929/6250000000000000000)
  directionLo := (468735185663420912363/100000000000000000000)
  directionHi := (117183796415855228091/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree089.table
  base := (1456945636245038253271729912064899737299/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-19687204217077173146631888872138429250000000000)
      constant := (461380282621081446933928831194937529608293573940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree089.table
  base := (7284728061081232201566205614880250654183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-6569761331267883066453575898824528500000000000)
      constant := (154132742135190750535621001629992490061188457532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468735185663420912363/100000000000000000000)
  centralHi := (117183796415855228091/25000000000000000000)
  directionLo := (3682741643340074313/781250000000000000)
  directionHi := (94278186069505902413/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree090.table
  base := (30511795640106203563675661552081378968969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-6636103204230610214547896716931778500000000000)
      constant := (157331204143420530245227861805957415017454797569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree090.table
  base := (3051179522961891834476674610330955643957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-6643545825599085288501437893673966000000000000)
      constant := (157678184902861501262440991630655402030253997570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3682741643340074313/781250000000000000)
  centralHi := (94278186069505902413/20000000000000000000)
  directionLo := (4740317965589409343/1000000000000000000)
  directionHi := (474031796558940934301/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree091.table
  base := (997190358343270382084318127258983355499/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (193614)
      previous := (96807)
      next := (96807)
      square := (1264100613968689483801455249750000000000000)
      linear := (-119108964546192237518671546919835750000000000)
      constant := (2856379749324725805997922556386675609163161216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree091.table
  base := (31910091116407289059439328396017175894483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3792301841906068451404365749250000000000000)
      linear := (-357727650173802293461205319507163500000000000)
      constant := (8588030331022344039728152004144320180683633563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4740317965589409343/1000000000000000000)
  centralHi := (474031796558940934301/100000000000000000000)
  directionLo := (14895563487339321191/3125000000000000000)
  directionHi := (476658031594858278113/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree092.table
  base := (33333800107020231446884689212408681977117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (61854)
      previous := (30927)
      next := (30927)
      square := (403843107298125751913886459750000000000000)
      linear := (-38469792824047534286705657293212000000000000)
      constant := (933050998509471462966773126983110826762398319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree092.table
  base := (16666899903822597155563802341233877034797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (61854)
      previous := (30927)
      next := (30927)
      square := (403843107298125751913886459750000000000000)
      linear := (-38512938455169128918320388752587000000000000)
      constant := (935107161052111841126258014988765151313284158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14895563487339321191/3125000000000000000)
  centralHi := (476658031594858278113/100000000000000000000)
  directionLo := (479269875976857801493/100000000000000000000)
  directionHi := (239634937988428900747/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree093.table
  base := (4347865184628991146575024424110398772321/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-6857208599845267711559697995588684750000000000)
      constant := (168187004711615807282573713889668457030466657768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree093.table
  base := (17391460610705624303332544550259296141223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-20594697925778075863935071634666835500000000000)
      constant := (505672493333538291587213024971062132474678864538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479269875976857801493/100000000000000000000)
  centralHi := (239634937988428900747/50000000000000000000)
  directionLo := (481867563707976099621/100000000000000000000)
  directionHi := (240933781853988049811/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree094.table
  base := (906436387669785285985667877663623299669/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-20792731195150460631690895265422960500000000000)
      constant := (515659285387054265174284588083594950362394992280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree094.table
  base := (36257455288555521314423486104785559043291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-62448154226315047590235972857645444000000000000)
      constant := (1550384372119877634861276692827962436751263328219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481867563707976099621/100000000000000000000)
  centralHi := (240933781853988049811/50000000000000000000)
  directionLo := (484451322517389925811/100000000000000000000)
  directionHi := (121112830629347481453/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree095.table
  base := (37757402137010730355617885076293464725773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-21013836590765118128702696544079866750000000000)
      constant := (526878791952229728400703273547826195143283995919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree095.table
  base := (37757401950713151833257137613216425115717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-21037404891765289196222243603763460500000000000)
      constant := (528038580300176293347619038909252150334060646551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484451322517389925811/100000000000000000000)
  centralHi := (121112830629347481453/25000000000000000000)
  directionLo := (121755343523353190051/25000000000000000000)
  directionHi := (97404274818682552041/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree096.table
  base := (7856552263528500036950415303555025255283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-7078313995459925208571499274245591000000000000)
      constant := (179406511272316984176770569318949700064237777415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree096.table
  base := (19641380579313378497670949307465797986181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-21258758374758895862365829588311773000000000000)
      constant := (539403862100978558831033509706503206834575405486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121755343523353190051/25000000000000000000)
  centralHi := (97404274818682552041/20000000000000000000)
  directionLo := (489577934305482811909/100000000000000000000)
  directionHi := (48957793430548281191/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree097.table
  base := (8166706601288805630869786722971517762789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-21456047381994433122726299101393679250000000000)
      constant := (549681510969888320633452342439709526791103990835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree097.table
  base := (40833532870729634199740841130801198674433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-64440335573257507585528246718580256500000000000)
      constant := (1652671908293653081198969669318862237320486861697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489577934305482811909/100000000000000000000)
  centralHi := (48957793430548281191/10000000000000000000)
  directionLo := (98424242683154314477/20000000000000000000)
  directionHi := (246060606707885786193/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree098.table
  base := (42409717167764418406952539048935444003969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-21677152777609090619738100380050585500000000000)
      constant := (561264723401480155488467927603805548606946497707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree098.table
  base := (8481943410389844736093744144560590257963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-7233821780248703064884333852469466000000000000)
      constant := (187499634093829044102190546198197959023260750815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98424242683154314477/20000000000000000000)
  centralHi := (246060606707885786193/50000000000000000000)
  directionLo := (494651416280999984493/100000000000000000000)
  directionHi := (247325708140499992247/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree099.table
  base := (22005656885760014996927782830701092926751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-7299419391074582705583300552902497250000000000)
      constant := (190989723701219311447330770727739141637801432302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree099.table
  base := (22005656836348296887721066512635467622987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-7307606274579905286932195847318903500000000000)
      constant := (191409553547950344771071000290112634788175321574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494651416280999984493/100000000000000000000)
  centralHi := (247325708140499992247/50000000000000000000)
  directionLo := (497168742545010448911/100000000000000000000)
  directionHi := (31073046409063153057/6250000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree100.table
  base := (45638322792329044523470405922449598063847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-22119363568838405613761702937364398000000000000)
      constant := (584794854069614177355946525075628002674517956941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree100.table
  base := (11409580677003258571124846345120304475281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-66432516920199967580820520579515069000000000000)
      constant := (1758239733534846196403300030432919887254205480516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497168742545010448911/100000000000000000000)
  centralHi := (31073046409063153057/6250000000000000000)
  directionLo := (499673386822606982349/100000000000000000000)
  directionHi := (9993467736452139647/2000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree101.table
  base := (9458148841756087873227820857404320510763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-22340468964453063110773504216021304250000000000)
      constant := (596741772293606384027988413629986606580678344445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree101.table
  base := (4729074413684933718161504235855512961269/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-22365525789726929193083759511053335500000000000)
      constant := (598052653879134765030028566557900302396262296070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499673386822606982349/100000000000000000000)
  centralHi := (9993467736452139647/2000000000000000000)
  directionLo := (502165538875142621433/100000000000000000000)
  directionHi := (251082769437571310717/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree102.table
  base := (24484289001408248863759561363456630521941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-7520524786689240202595101831559403500000000000)
      constant := (202936641923597140180241642039838195856834094682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree102.table
  base := (24484288970728569809954415570458594075779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-22586879272720535859227345495601648000000000000)
      constant := (610146888741648968839376840300358524238812310274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502165538875142621433/100000000000000000000)
  centralHi := (251082769437571310717/50000000000000000000)
  directionLo := (63080672972287800819/12500000000000000000)
  directionHi := (504645383778302406553/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree103.table
  base := (50671824159211226865004723651512411403129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-22782679755682378104797106773335116750000000000)
      constant := (620999314497085629962610975905196991923990907187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree103.table
  base := (25335912053437454950652047250692909568231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-68424698267142427576112794440449881500000000000)
      constant := (1867087847285435847629376733020943153455819553358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63080672972287800819/12500000000000000000)
  centralHi := (504645383778302406553/100000000000000000000)
  directionLo := (50711310208250177687/10000000000000000000)
  directionHi := (507113102082501776871/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree104.table
  base := (26200241332564896339191544329965062449731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (193614)
      previous := (96807)
      next := (96807)
      square := (1264100613968689483801455249750000000000000)
      linear := (-136117071901165891134963952970367000000000000)
      constant := (3747396085615660776825249612150652108215446194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree104.table
  base := (52400482620493864565864544226672763131743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (193614)
      previous := (96807)
      next := (96807)
      square := (1264100613968689483801455249750000000000000)
      linear := (-136269741057442302908369925826617000000000000)
      constant := (3755620325066520666218754357219522675090076141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50711310208250177687/10000000000000000000)
  centralHi := (507113102082501776871/100000000000000000000)
  directionLo := (509568869966293775241/100000000000000000000)
  directionHi := (254784434983146887621/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree105.table
  base := (27077276754878195474017189703799945739801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-7741630182303897699606903110216309750000000000)
      constant := (215247265894591237788059617420258819655980398402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree105.table
  base := (5415455347169139142840243285897117959161/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-23250939721701355857658103449246585500000000000)
      constant := (647158546262090082527004656958287198998758576830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509568869966293775241/100000000000000000000)
  centralHi := (254784434983146887621/50000000000000000000)
  directionLo := (512012859383153931121/100000000000000000000)
  directionHi := (256006429691576965561/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree106.table
  base := (55934036683979928588965769819109903248901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-23445995942526350595832510609305835500000000000)
      constant := (658294892138823133706071648395242076849814994903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree106.table
  base := (27967018325760742327787823776661301454603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-70416879614084887571405068301384694000000000000)
      constant := (1979216249210870620246133704240564769579173330454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512012859383153931121/100000000000000000000)
  centralHi := (256006429691576965561/50000000000000000000)
  directionLo := (64305654775248613393/12500000000000000000)
  directionHi := (102889047640397781429/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree107.table
  base := (28869466090064269081501085035595687359551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-23667101338141008092844311887962741750000000000)
      constant := (670969221832137314446624699240986901859724813706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree107.table
  base := (57738932152453329073865781997962760325761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-7897882229229523063315091806114403500000000000)
      constant := (224146815119607526011368687535922797142133359161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64305654775248613393/12500000000000000000)
  centralHi := (102889047640397781429/20000000000000000000)
  directionLo := (516866170341693820891/100000000000000000000)
  directionHi := (129216542585423455223/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree108.table
  base := (1861538749742041956854444663277530247059/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-7962735577918555196618704388873216000000000000)
      constant := (227921595587328167263393976690709383286754293088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree108.table
  base := (7446154996018818560094290983218820630601/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-7971666723560725285362953800963841000000000000)
      constant := (228421211041995920425515023017387794265570880008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516866170341693820891/100000000000000000000)
  centralHi := (129216542585423455223/25000000000000000000)
  directionLo := (519275815900063460139/100000000000000000000)
  directionHi := (25963790795003173007/5000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree109.table
  base := (12284992022679812916390829266815159698449/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-24109312129370323086867914445276554250000000000)
      constant := (696681586926908010850659483779518188968953085735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree109.table
  base := (61424960093284796200341009754500316880907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-72409060961027347566697342162319506500000000000)
      constant := (2094624939111070033737535317549042457871479700363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519275815900063460139/100000000000000000000)
  centralHi := (25963790795003173007/5000000000000000000)
  directionLo := (260837165638672140577/50000000000000000000)
  directionHi := (104334866255468856231/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree110.table
  base := (63306092540524069063776362846862765524753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-24330417524984980583879715723933460500000000000)
      constant := (709719622325683324627622489174858269770785328859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree110.table
  base := (63306092523378348758834673142420783854593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-24357707136669389188376033371988148000000000000)
      constant := (711274485090728389073164963984112727117153406379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260837165638672140577/50000000000000000000)
  centralHi := (104334866255468856231/20000000000000000000)
  directionLo := (524061869294697009273/100000000000000000000)
  directionHi := (262030934647348504637/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree111.table
  base := (32606318634642634320007544997272316310829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-8183840973533212693630505667530122250000000000)
      constant := (240959630985760620389492992576339162458821346858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree111.table
  base := (16303159313667798365214877869093406230609/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-24579060619662995854519619356536460500000000000)
      constant := (724462149286094448073566766010487743793822102508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524061869294697009273/100000000000000000000)
  centralHi := (262030934647348504637/50000000000000000000)
  directionLo := (263219289653911876023/50000000000000000000)
  directionHi := (526438579307823752047/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree112.table
  base := (6714459429646402982802576698746820872177/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-24772628316214295577903318281247273000000000000)
      constant := (736159398820840373317283230304528486983804879310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree112.table
  base := (671445942840088015621049398294319264693/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-74401242307969807561989616023254319000000000000)
      constant := (2213313916866826402522720540358947870924537003700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263219289653911876023/50000000000000000000)
  centralHi := (526438579307823752047/100000000000000000000)
  directionLo := (13220115182899967471/2500000000000000000)
  directionHi := (528804607315998698841/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree113.table
  base := (55281570895489455159789951371871126237/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-24993733711828953074915119559904179250000000000)
      constant := (749561139915635106245975582661912328236115138750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree113.table
  base := (13820392721749474141173333309989559265279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-25021767585650209186806791325633085500000000000)
      constant := (751201954098562371651710045177750447036878118185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13220115182899967471/2500000000000000000)
  centralHi := (528804607315998698841/100000000000000000000)
  directionLo := (66395012008340954477/12500000000000000000)
  directionHi := (531160096066727635817/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree114.table
  base := (14216949047143766440177348505354044777287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-8404946369147870190642306946187028500000000000)
      constant := (254361372080353324598280395915359000191921175435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree114.table
  base := (7108474522667382025286549039779597454161/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-25243121068643815852950377310181398000000000000)
      constant := (764754094714361605639279761574585898884983426830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66395012008340954477/12500000000000000000)
  centralHi := (531160096066727635817/100000000000000000000)
  directionLo := (266752592578124288597/50000000000000000000)
  directionHi := (106701037031249715439/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree115.table
  base := (73092939143645282470257327680982690214063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (61854)
      previous := (30927)
      next := (30927)
      square := (403843107298125751913886459750000000000000)
      linear := (-48083070894250034156783973756555750000000000)
      constant := (1468295515683569242705653094595832559876029941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree115.table
  base := (73092939135938245386091843369575439566089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (185562)
      previous := (92781)
      next := (92781)
      square := (1211529321894377255741659379250000000000000)
      linear := (-144411008799456082338907164242323500000000000)
      constant := (4414523974305351717100073225763361899830021369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266752592578124288597/50000000000000000000)
  centralHi := (106701037031249715439/20000000000000000000)
  directionLo := (535840011126073734407/100000000000000000000)
  directionHi := (66980001390759216801/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree116.table
  base := (15025309068312675369797373526673117928249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-25657049898672925565950523395874898000000000000)
      constant := (790493774581856404243787877847055972363550832735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree116.table
  base := (15025309066999378498669928960549026410199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-8561942678210343061745849759759341000000000000)
      constant := (264074284120864857909919223820291898550491003995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535840011126073734407/100000000000000000000)
  centralHi := (66980001390759216801/12500000000000000000)
  directionLo := (107632941511152350327/20000000000000000000)
  directionHi := (134541176888940437909/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree117.table
  base := (38592781914079162028473685666264866845369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (421366871322896494600485083250000000000000)
      linear := (-51041726418713181583752119673632750000000000)
      constant := (1586549224056118673346408663865291736934900402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree117.table
  base := (19296390955641004880123489792916963374269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (421366871322896494600485083250000000000000)
      linear := (-51098977352316835998779359494726500000000000)
      constant := (1590018677306251338474292318314816700749953204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107632941511152350327/20000000000000000000)
  centralHi := (134541176888940437909/25000000000000000000)
  directionLo := (540479405152098571673/100000000000000000000)
  directionHi := (270239702576049285837/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree118.table
  base := (39634997301168484450706232366782605041549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-26099260689902240559974125953188710500000000000)
      constant := (818388373840102231317659639541169265758667132894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree118.table
  base := (79269994597571259363454886833260996142663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-78385605001854727552574163745123944000000000000)
      constant := (2460532735691745134449076963869524735720351933767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540479405152098571673/100000000000000000000)
  centralHi := (270239702576049285837/50000000000000000000)
  directionLo := (67848028979356925931/12500000000000000000)
  directionHi := (542784231834855407449/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree119.table
  base := (3255193506527714749259068919102382789287/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-26320366085516898056985927231845616750000000000)
      constant := (832517526312563485398578431068020142179316031525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree119.table
  base := (81379837659133319203361408006222102621817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-26349888483611849183668307232922960500000000000)
      constant := (834337179871293984169536355055159566558229184851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67848028979356925931/12500000000000000000)
  centralHi := (542784231834855407449/100000000000000000000)
  directionLo := (272539656409641516523/50000000000000000000)
  directionHi := (545079312819283033047/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree120.table
  base := (83515093009976810876317427051069630284187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-8847157160377185184665909503500841000000000000)
      constant := (282255971337878329514477633817564346017036601987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree120.table
  base := (83515093006519030131851003237601994547979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-26571241966605455849811893217471273000000000000)
      constant := (848618273316210144971268753876726702743751611737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272539656409641516523/50000000000000000000)
  centralHi := (545079312819283033047/100000000000000000000)
  directionLo := (109472954139098585839/20000000000000000000)
  directionHi := (136841192673873232299/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree121.table
  base := (42837880321035962753816611300601295703299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-26762576876746213051009529789159429250000000000)
      constant := (861139536943151294413663142553679045646461303394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree121.table
  base := (85675760639126914653252709927510958390801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-80377786348797187547866437606058756500000000000)
      constant := (2589062576695506627458354235717094298876114001809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109472954139098585839/20000000000000000000)
  centralHi := (136841192673873232299/25000000000000000000)
  directionLo := (68705090688108460073/12500000000000000000)
  directionHi := (109928145100973536117/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree122.table
  base := (87861840558972679682444822988074234943119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-26983682272360870548021331067816335500000000000)
      constant := (875632395100976817557363280756301298003199345157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree122.table
  base := (87861840556464569070345172102543922607457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-27013948932592669182099065186567898000000000000)
      constant := (877544936618038112565278469805938596800087789771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68705090688108460073/12500000000000000000)
  centralHi := (109928145100973536117/20000000000000000000)
  directionLo := (275953647406817694121/50000000000000000000)
  directionHi := (551907294813635388243/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree123.table
  base := (45036666380133574624599127735465628826927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-9068262555991842681677710782157747250000000000)
      constant := (296748829495667026227104695303190512310824701454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree123.table
  base := (1407395824345801047860656946841355686703/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-27235302415586275848242651171116210500000000000)
      constant := (892190506474710379207534537665198823850161501376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275953647406817694121/50000000000000000000)
  centralHi := (551907294813635388243/100000000000000000000)
  directionLo := (277082296891867847191/50000000000000000000)
  directionHi := (554164593783735694383/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree124.table
  base := (46155118622811029501649005398120661701293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-27425893063590185542044933625130148000000000000)
      constant := (904981817101134692375817428645164629285543772958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree124.table
  base := (23077559310950820770471166048058327291223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-82369967695739647543158711466993569000000000000)
      constant := (2720872705405296554747937907814700956653854587228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277082296891867847191/50000000000000000000)
  centralHi := (554164593783735694383/100000000000000000000)
  directionLo := (139103183810274571861/25000000000000000000)
  directionHi := (111282547048219657489/20000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree125.table
  base := (11821569251846270078986339949007917141827/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-27646998459204843039056734903787054250000000000)
      constant := (919838380943305981841621096737417857545452915048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree125.table
  base := (47286277006610756069837717929585342399529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-9226003127191163060176607713404278500000000000)
      constant := (307282040866378012318587864135380628547970584258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139103183810274571861/25000000000000000000)
  centralHi := (111282547048219657489/20000000000000000000)
  directionLo := (139662957435362107899/25000000000000000000)
  directionHi := (558651829741448431597/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree126.table
  base := (24215070766874896212710043915679433537923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-9289367951606500178689512060814653500000000000)
      constant := (311605393337819374367037302425343791807145416492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree126.table
  base := (96860283066181028430157893654328834471407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-9299787621522365282224469708253716000000000000)
      constant := (312285389622253657870287092004418790005578257207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139662957435362107899/25000000000000000000)
  centralHi := (558651829741448431597/100000000000000000000)
  directionLo := (280440992816874060093/50000000000000000000)
  directionHi := (560881985633748120187/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree127.table
  base := (99173424403644860617600206022244753924147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-28089209250434158033080337461100866750000000000)
      constant := (949915214311546736324265849027651817260155497841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree127.table
  base := (99173424402522280807672146501866539175173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (640899011282125568287337811623250000000000000)
      linear := (-84362149042682107538450985327928381500000000000)
      constant := (2855963121813810608356058800980089788625446772357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280440992816874060093/50000000000000000000)
  centralHi := (560881985633748120187/100000000000000000000)
  directionLo := (56310330912137586103/10000000000000000000)
  directionHi := (563103309121375861031/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree128.table
  base := (101511978023079342014066012372451732323501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-28310314646048815530092138739757773000000000000)
      constant := (965135483837537854695909460774309015964359938703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree128.table
  base := (50755989011061835063608246405556175375393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-28342069830554309178960581093857773000000000000)
      constant := (967240737812629111223751673974739709808413057558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell095.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56310330912137586103/10000000000000000000)
  centralHi := (563103309121375861031/100000000000000000000)
  directionLo := (565315904321142839421/100000000000000000000)
  directionHi := (282657952160571419711/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree129.table
  base := (25968985981427205923792028162449724056049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (71211001253569507587481979069250000000000000)
      linear := (-9510473347221157675701313339471559750000000000)
      constant := (326825662863802070686626357406038471254151846596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree129.table
  base := (103875943924895293105599615519276818842453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (32720766)
      previous := (16360383)
      next := (16360383)
      square := (213633003760708522762445937207750000000000000)
      linear := (-28563423313547915845104167078406085500000000000)
      constant := (982615260490813586595795736147194391862752421959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell095.Kernel129
