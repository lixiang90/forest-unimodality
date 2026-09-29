import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell169.Parameters
import ForestUnimodality.BinomialMassData.Q27_47.Batch000_049
import ForestUnimodality.BinomialMassData.Q27_47.Batch050_099
import ForestUnimodality.BinomialMassData.Q27_47.Batch100_149
import ForestUnimodality.BinomialMassData.Q653_1128.Batch000_049
import ForestUnimodality.BinomialMassData.Q653_1128.Batch050_099
import ForestUnimodality.BinomialMassData.Q653_1128.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree000.table
  base := (461490807183028590054751923/25000000000000000000000000)
  polynomial :=
    { denominator := 117500000000000000000000000000000000000000
      center := (297)
      previous := (0)
      next := (220)
      square := (6985227497723170350663046690000000000000)
      linear := (-24009153742042060528105729000000000000000)
      constant := (2169006793760234373257334038100000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree000.table
  base := (461490807183028590054751923/25000000000000000000000000)
  polynomial :=
    { denominator := 2820000000000000000000000000000000000000000
      center := (7183)
      previous := (0)
      next := (5225)
      square := (167645459945356088415913120560000000000000)
      linear := (-576219689809009452674537496000000000000000)
      constant := (52056163050245624958176016914400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree001.table
  base := (27682072808505494237258496368121155641693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-1505632510753028043756773784260000000000000)
      constant := (61906291322169308387035923395009632812499837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree001.table
  base := (55082210184347574109945241779105786460691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-108615097599149714261007603867420000000000000)
      constant := (4435313327306452623035482506618662312499991084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24686771664426040853/50000000000000000000)
  directionHi := (49373543328852081707/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree002.table
  base := (13749361676058897405445793619193148373447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-7531339182520316970770313222080000000000000)
      constant := (158781202314680182639988431745268323784722115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree002.table
  base := (68112750845783468380474628073105088165207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-135983218935229095694905420798840000000000000)
      constant := (2834053913194306034660102312729019515624960734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24686771664426040853/50000000000000000000)
  centralHi := (49373543328852081707/100000000000000000000)
  directionLo := (69824734598078264399/100000000000000000000)
  directionHi := (174561836495195661/250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree003.table
  base := (8864076053253427264172540917808936805823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-9040148322028521766513531307120000000000000)
      constant := (109583117957845027120121779087079707020315035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree003.table
  base := (43775241838017475378903356583838320332201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-54450446757102825709601079243420000000000000)
      constant := (650996124778951244071458140071354347682992054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69824734598078264399/100000000000000000000)
  centralHi := (174561836495195661/250000000000000000)
  directionLo := (21379371398818800551/25000000000000000000)
  directionHi := (17103497119055040441/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree004.table
  base := (3705170855570466069115727939465687763703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-2637239365384181640564187348040000000000000)
      constant := (20695958838379437353157508525839408540039854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree004.table
  base := (29213807252997329620553964036348842921813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-190719461607387858562701054661680000000000000)
      constant := (1476482531528093293736910830714162692257128506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21379371398818800551/25000000000000000000)
  centralHi := (17103497119055040441/20000000000000000000)
  directionLo := (98747086657704163413/100000000000000000000)
  directionHi := (49373543328852081707/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree005.table
  base := (20442783751305468964594411249316322933871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-12057766601044931357999967477200000000000000)
      constant := (68957586041890091895271171592739757360921039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree005.table
  base := (10058902364796073992987227814298075450707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-218087582943467239996598871593100000000000000)
      constant := (1233136623204738544632061326910583902142023468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98747086657704163413/100000000000000000000)
  centralHi := (49373543328852081707/50000000000000000000)
  directionLo := (22080519834668901661/20000000000000000000)
  directionHi := (55201299586672254153/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree006.table
  base := (1438559725237559787456372467037898184317/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-6783287870276568076871592781120000000000000)
      constant := (31468722252149066216021507002193585445781265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree006.table
  base := (14138869051414502406783883182454159912409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-81818568093182207143498896174840000000000000)
      constant := (376524983877597523348287549114892435479068886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22080519834668901661/20000000000000000000)
  centralHi := (55201299586672254153/50000000000000000000)
  directionLo := (120939987948883984541/100000000000000000000)
  directionHi := (60469993974441992271/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree007.table
  base := (10175782905865320941030437980603664036323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-15075384880061340949486403647280000000000000)
      constant := (61864910748565344321902014649833493856237507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree007.table
  base := (9985486452875835647614003151976531410273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-272823825615626002864394505455940000000000000)
      constant := (1114444346464923157182602692142524591935275026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120939987948883984541/100000000000000000000)
  centralHi := (60469993974441992271/50000000000000000000)
  directionLo := (130630116994214765619/100000000000000000000)
  directionHi := (6531505849710738281/5000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree008.table
  base := (7089504180783269441489577472545025671321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-16584194019569545745229621732320000000000000)
      constant := (64141029877731794056834686609331961707948089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree008.table
  base := (3469580672367030452287479580116984446711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-300191946951705384298292322387360000000000000)
      constant := (1159175986081686450549012992044663071140245564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130630116994214765619/100000000000000000000)
  centralHi := (6531505849710738281/5000000000000000000)
  directionLo := (69824734598078264399/50000000000000000000)
  directionHi := (139649469196156528799/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree009.table
  base := (1178860585337124532101920703759577329833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-4523250789769437635243209954340000000000000)
      constant := (17214299701114343396259904002834906321601097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree009.table
  base := (2296776537933147438904670286453356280181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-109186689429261588577396713106260000000000000)
      constant := (415870984504378121458387728469756818275037948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69824734598078264399/50000000000000000000)
  centralHi := (139649469196156528799/100000000000000000000)
  directionLo := (231438484353994133/156250000000000000)
  directionHi := (148120629986556245121/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree010.table
  base := (2814745389610083899961716846819211753783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-19601812298585955336716057902400000000000000)
      constant := (75485793465268493774589713766623638764106647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree010.table
  base := (271359333669418875150618375097427549361/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-354928189623864147166087956250200000000000000)
      constant := (1370408462633812593046777736021614142176920820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231438484353994133/156250000000000000)
  centralHi := (148120629986556245121/100000000000000000000)
  directionLo := (156132853072184455669/100000000000000000000)
  directionHi := (15613285307218445567/10000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree011.table
  base := (311174584518449095909063876932618572949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-5277655359523540033114818996860000000000000)
      constant := (20927889113197599933149602031574154427644341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree011.table
  base := (1159182262706189597488683302197545784693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-382296310959943528599985773181620000000000000)
      constant := (1521991862631012769033690507875482565490963066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156132853072184455669/100000000000000000000)
  centralHi := (15613285307218445567/10000000000000000000)
  directionLo := (4093837944803932157/2500000000000000000)
  directionHi := (163753517792157286281/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree012.table
  base := (-83050995195142492997465771263945266113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-22619430577602364928202494072480000000000000)
      constant := (93339317797129166697070558157357944907156383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree012.table
  base := (-1221252547400429692981818003732430467/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-136554810765340970011294530037680000000000000)
      constant := (566306055556261849717559383189431886923568896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4093837944803932157/2500000000000000000)
  centralHi := (163753517792157286281/100000000000000000000)
  directionLo := (171034971190550404409/100000000000000000000)
  directionHi := (17103497119055040441/10000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree013.table
  base := (-612748218410235624450990561657629292127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-12064119858555284861972856078760000000000000)
      constant := (52121589067636478139808962979838296893691457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree013.table
  base := (-1288823657303340090818406128971395894809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-437032553632102291467781407044460000000000000)
      constant := (1898964312036230303914965124905923106430604542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171034971190550404409/100000000000000000000)
  centralHi := (17103497119055040441/10000000000000000000)
  directionLo := (178018842123519162951/100000000000000000000)
  directionHi := (22252355265439895369/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree014.table
  base := (-2221057080186516112290774300229354204119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-25637048856618774519688930242560000000000000)
      constant := (116338269689935791842116925925513356563101129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree014.table
  base := (-2276071674179275480455323253059662816559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-464400674968181672901679223975880000000000000)
      constant := (2120629524064734816951006508512376687087981042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178018842123519162951/100000000000000000000)
  centralHi := (22252355265439895369/12500000000000000000)
  directionLo := (92369441553801323477/50000000000000000000)
  directionHi := (36947776621520529391/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree015.table
  base := (-3096774324218377859100609873726177235271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-27145857996126979315432148327600000000000000)
      constant := (129564858010892125770523245115938874487286361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree015.table
  base := (-628937359923423905742086718465743901959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-163922932101420351445192346969100000000000000)
      constant := (787618413991357401262115748676306401617177070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92369441553801323477/50000000000000000000)
  centralHi := (36947776621520529391/20000000000000000000)
  directionLo := (38244582211178884063/20000000000000000000)
  directionHi := (47805727763973605079/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree016.table
  base := (-774487649164255703147910557094396862619/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-28654667135635184111175366412640000000000000)
      constant := (143879226818258322608501468074812386652373145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree016.table
  base := (-978548887164635860111601586537138953203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-519136917640340435769474857838720000000000000)
      constant := (2624865052473155533973237884750201123770969256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38244582211178884063/20000000000000000000)
  centralHi := (47805727763973605079/25000000000000000000)
  directionLo := (98747086657704163413/50000000000000000000)
  directionHi := (197494173315408326827/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree017.table
  base := (-2281506142323526222443268793980414227497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-15081738137571694453459292248840000000000000)
      constant := (79624160936921740124446914187837264971459127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree017.table
  base := (-45993899519379132392449580616883435997/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-546505038976419817203372674770140000000000000)
      constant := (2906070794839901145682022211327681831788728600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98747086657704163413/50000000000000000000)
  centralHi := (197494173315408326827/100000000000000000000)
  directionLo := (203572334255867332797/100000000000000000000)
  directionHi := (101786167127933666399/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree018.table
  base := (-5180103670178279343085906600849844326693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-31672285414651593702661802582720000000000000)
      constant := (175646502807720580142033873834402693882335163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree018.table
  base := (-2605879824112867969352833214011991470669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-191291053437499732879090163900520000000000000)
      constant := (1068671872685838713012651272562775130095506148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203572334255867332797/100000000000000000000)
  centralHi := (101786167127933666399/50000000000000000000)
  directionLo := (104737101897117396599/50000000000000000000)
  directionHi := (209474203794234793199/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree019.table
  base := (-1146577946704528858794701793164048058587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-33181094554159798498405020667760000000000000)
      constant := (193053496895472745938170013697023089192906585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree019.table
  base := (-11250772771474869811916467749709654277/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-601241281648578580071168308632980000000000000)
      constant := (3524338044930186244835684404734458650038618112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104737101897117396599/50000000000000000000)
  centralHi := (209474203794234793199/100000000000000000000)
  directionLo := (53803571463748252353/25000000000000000000)
  directionHi := (215214285854993009413/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree020.table
  base := (-3114363419891761745911656550440314154431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-17344951846834001647074119376400000000000000)
      constant := (105726526963293309812075525864077346032861921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree020.table
  base := (-6252586437846199668605255485530327451869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-628609402984657961505066125564400000000000000)
      constant := (3860748271965864516923290800025843119858784822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53803571463748252353/25000000000000000000)
  centralHi := (215214285854993009413/100000000000000000000)
  directionLo := (22080519834668901661/10000000000000000000)
  directionHi := (220805198346689016611/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree021.table
  base := (-26068627499428937373994008016862141879/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-9049678208294052022472864209460000000000000)
      constant := (57708005571559951228065325025638097829714496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree021.table
  base := (-6694228958700288753756473231222529238179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-218659174773579114312987980831940000000000000)
      constant := (1405003941229163361300408076680277847477175534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22080519834668901661/10000000000000000000)
  centralHi := (220805198346689016611/100000000000000000000)
  directionLo := (226257999632646606531/100000000000000000000)
  directionHi := (56564499908161651633/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree022.table
  base := (-3536132763525558999763885168424573504777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-18853760986342206442817337461440000000000000)
      constant := (125589843727796839304423811030390117127947607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree022.table
  base := (-7090124297521673621057949292839653731913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-683345645656816724372861759427240000000000000)
      constant := (4586937799712571521872575041430124688311675294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226257999632646606531/100000000000000000000)
  centralHi := (56564499908161651633/25000000000000000000)
  directionLo := (231582445747972758207/100000000000000000000)
  directionHi := (3618475714812074347/1562500000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree023.table
  base := (-7428786947568761770885168439346978345591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-39216331112192617681377893007920000000000000)
      constant := (272487280928007222936103590653762524834589481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree023.table
  base := (-1861049474886704296416194398000211830183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-710713766992896105806759576358660000000000000)
      constant := (4976370116487616592404946389682296058833054216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231582445747972758207/100000000000000000000)
  centralHi := (3618475714812074347/1562500000000000000)
  directionLo := (23678719551415524069/10000000000000000000)
  directionHi := (236787195514155240691/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree024.table
  base := (-1936597842723860263884869171753897080353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-10181285062925205619280277773240000000000000)
      constant := (73686901186094973918967771653675641349500223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree024.table
  base := (-7759668488836828181127228836635718354193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-246027296109658495746885797763360000000000000)
      constant := (1794393597035502496678304136969550188933525978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23678719551415524069/10000000000000000000)
  centralHi := (236787195514155240691/100000000000000000000)
  directionLo := (120939987948883984541/50000000000000000000)
  directionHi := (241879975897767969083/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree025.table
  base := (-250867475400512109506145745581997042619/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-10558487347802256818216082294500000000000000)
      constant := (79488684466560530027935156227824948262837032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree025.table
  base := (-8039180431831473985290513948331635730127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-765450009665054868674555210221500000000000000)
      constant := (5807264678270866184284591828445031250098690226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120939987948883984541/50000000000000000000)
  centralHi := (241879975897767969083/100000000000000000000)
  directionLo := (246867716644260408533/100000000000000000000)
  directionHi := (123433858322130204267/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree026.table
  base := (-8275098525323351970303011740829598292637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-43742758530717232068607547263040000000000000)
      constant := (342103802706744118608449369076827417371564867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree026.table
  base := (-8284909106003819864714099241280384734521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-792818131001134250108453027152920000000000000)
      constant := (6248535280621608654025047142706544342185975998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246867716644260408533/100000000000000000000)
  centralHi := (123433858322130204267/50000000000000000000)
  directionLo := (251756660889035628003/100000000000000000000)
  directionHi := (62939165222258907001/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree027.table
  base := (-1698046006193302773677242145798036165723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-45251567670225436864350765348080000000000000)
      constant := (367190777289772544839305651027940690549589465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree027.table
  base := (-424932285668213651066184545160077101277/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-273395417445737877180783614694780000000000000)
      constant := (2235640458794799029364436141419028011993492840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251756660889035628003/100000000000000000000)
  centralHi := (62939165222258907001/25000000000000000000)
  directionLo := (256552456785825606613/100000000000000000000)
  directionHi := (128276228392912803307/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree028.table
  base := (-8674656103411993603056009163077527035043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-46760376809733641660093983433120000000000000)
      constant := (393212342871898938830526536681641742779590013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree028.table
  base := (-271308314783929910370835923185628932933/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-847554373673293012976248661015760000000000000)
      constant := (7182364284037277695254543144407516715798977728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256552456785825606613/100000000000000000000)
  centralHi := (128276228392912803307/50000000000000000000)
  directionLo := (130630116994214765619/50000000000000000000)
  directionHi := (261260233988429531239/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree029.table
  base := (-4414808521164345118474372231122432443553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-24134592974620923227918600759080000000000000)
      constant := (210082879815577351276374178339510546732191423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree029.table
  base := (-4417893355965305865830220685744541454257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-874922495009372394410146477947180000000000000)
      constant := (7674815632043126330905470140157054835391666332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130630116994214765619/50000000000000000000)
  centralHi := (261260233988429531239/100000000000000000000)
  directionLo := (26588466793806479873/10000000000000000000)
  directionHi := (265884667938064798731/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree030.table
  base := (-1119517145077311202048805164790603463769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-12444498772187512812895104900800000000000000)
      constant := (112012191215084892542859230618955113897068558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree030.table
  base := (-8961410760676533143649700037645392794867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-300763538781817258614681431626200000000000000)
      constant := (2728078511305320077951050986627172963896832782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26588466793806479873/10000000000000000000)
  centralHi := (265884667938064798731/100000000000000000000)
  directionLo := (135215017125854975291/50000000000000000000)
  directionHi := (270430034251709950583/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree031.table
  base := (-905506262803859678368649307331143182247/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-25643402114129128023661818844120000000000000)
      constant := (238429744685229937874069810089787523552081885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree031.table
  base := (-9059565600149439884445177364235710143201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-929658737681531157277942111810020000000000000)
      constant := (8710591091339379232040118865761913443286041838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135215017125854975291/50000000000000000000)
  centralHi := (270430034251709950583/100000000000000000000)
  directionLo := (274900255013026590231/100000000000000000000)
  directionHi := (34362531876628323779/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree032.table
  base := (-9127092602068916052417330285528585071593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-52795613367766460843066855773280000000000000)
      constant := (506596388722642510654157278686947355576851063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree032.table
  base := (-9130933791138789608045895807039524527333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-957026859017610538711839928741440000000000000)
      constant := (9253855164331272910228058726911534425744185254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274900255013026590231/100000000000000000000)
  centralHi := (34362531876628323779/12500000000000000000)
  directionLo := (279298938392313057597/100000000000000000000)
  directionHi := (139649469196156528799/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree033.table
  base := (-57330030430556147083257762202403704591/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-13576105626818666409702518464580000000000000)
      constant := (134314546646804219905217254400665608662339240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree033.table
  base := (-9176078515523826753551548719216196124229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-328131660117896640048579248557620000000000000)
      constant := (3271335119884586250343163512074019786569468834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279298938392313057597/100000000000000000000)
  centralHi := (139649469196156528799/50000000000000000000)
  directionLo := (283629412734150543981/100000000000000000000)
  directionHi := (141814706367075271991/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree034.table
  base := (-9192676981232627684943337695090679500749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-55813231646782870434553291943360000000000000)
      constant := (568843828050193955583348689773464688982845459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree034.table
  base := (-9195464519552120375663919640528303757687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1011763101689769301579635562604280000000000000)
      constant := (10391023198066540913691361976585448585986849506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283629412734150543981/100000000000000000000)
  centralHi := (141814706367075271991/50000000000000000000)
  directionLo := (143947378014298295049/50000000000000000000)
  directionHi := (287894756028596590099/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree035.table
  base := (-9187103694987970777189361235811480605249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-57322040786291075230296510028400000000000000)
      constant := (601352441095816876447374507317092439343004959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree035.table
  base := (-9189475364486735003312201980274600988999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1039131223025848683013533379535700000000000000)
      constant := (10984893428406677426414390459661165065475421762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143947378014298295049/50000000000000000000)
  centralHi := (287894756028596590099/100000000000000000000)
  directionLo := (9128056922119209943/3125000000000000000)
  directionHi := (292097821507814718177/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree036.table
  base := (-286137854978617148872351843543862807679/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-14707712481449820006509932028360000000000000)
      constant := (158695826204697394122719671148572856462696712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree036.table
  base := (-915842764179336853463217367249359153077/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-355499781453976021482477065489040000000000000)
      constant := (3865201154121436403124300394411989937851174420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9128056922119209943/3125000000000000000)
  centralHi := (292097821507814718177/100000000000000000000)
  directionLo := (231438484353994133/78125000000000000)
  directionHi := (296241259973112490241/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree037.table
  base := (-9100869796726747208830610331079308102723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-60339659065307484821782946198480000000000000)
      constant := (669135823181185730403626760791725808401084893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree037.table
  base := (-4551291345411156032291741700168919256253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1093867465698007445881329013398540000000000000)
      constant := (12223142908564189988049108596370350615065736428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231438484353994133/78125000000000000)
  centralHi := (296241259973112490241/100000000000000000000)
  directionLo := (150163769674398536627/50000000000000000000)
  directionHi := (60065507869759414651/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree038.table
  base := (-1127587764202502631421730820450849735217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-15462117051203922404381541070880000000000000)
      constant := (176102375835242456456099810283768145869811294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree038.table
  base := (-902215626025925707841890793616091864447/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1121235587034086827315226830329960000000000000)
      constant := (12867503188407079297606391789041984552858583860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150163769674398536627/50000000000000000000)
  centralHi := (60065507869759414651/20000000000000000000)
  directionLo := (30435896187257126381/10000000000000000000)
  directionHi := (304358961872571263811/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree039.table
  base := (-2229023200894807218764836202872102448273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-15839319336080973603317345592140000000000000)
      constant := (185150984437953890235553216641285525691764943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree039.table
  base := (-111466580947913297769230209340161411971/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-382867902790055402916374882420460000000000000)
      constant := (4509559073085915398989052391764691301658909280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30435896187257126381/10000000000000000000)
  centralHi := (304358961872571263811/100000000000000000000)
  directionLo := (12333507170500713479/4000000000000000000)
  directionHi := (19271104953907364811/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree040.table
  base := (-8787194441739112085591004807633085200151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-64866086483832099209012600453600000000000000)
      constant := (777718789375250291991867722571938514792866441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree040.table
  base := (-8788240412351497797652205666159699181201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1175971829706245590183022464192800000000000000)
      constant := (14206659153127684314172879948428158041157085838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12333507170500713479/4000000000000000000)
  centralHi := (19271104953907364811/6250000000000000000)
  directionLo := (312265706144368911339/100000000000000000000)
  directionHi := (15613285307218445567/5000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree041.table
  base := (-2158533304011981105853380686996238414171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-16593723905835076001188954634660000000000000)
      constant := (203938444865524081615180368814655309343096261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree041.table
  base := (-8635019515346090740664620695916770843599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1203339951042324971616920281124220000000000000)
      constant := (14901444161099668884420055502676311107716816562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312265706144368911339/100000000000000000000)
  centralHi := (15613285307218445567/5000000000000000000)
  directionLo := (316144931976913699141/100000000000000000000)
  directionHi := (158072465988456849571/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree042.table
  base := (-338280539924829981180580698514055430127/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-67883704762848508800499036623680000000000000)
      constant := (854708677455455944585832474629041288871236425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree042.table
  base := (-132152563660573196003002706289437186609/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-410236024126134784350272699351880000000000000)
      constant := (5204342751821399224778234704367352169835796096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316144931976913699141/100000000000000000000)
  centralHi := (158072465988456849571/50000000000000000000)
  directionLo := (79994282918973897081/25000000000000000000)
  directionHi := (12799085267035823533/4000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree043.table
  base := (-2063980405222675652094438597924162200881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-17348128475589178399060563677180000000000000)
      constant := (223645823161469973720124020706855525698253871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree043.table
  base := (-8256556913639517154977265958576372644693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1258076193714483734484715914987060000000000000)
      constant := (16341408142953651270678454360661470020901716934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79994282918973897081/25000000000000000000)
  centralHi := (12799085267035823533/4000000000000000000)
  directionLo := (12950559004236347343/4000000000000000000)
  directionHi := (40470496888238585447/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree044.table
  base := (-62741632820617154148045134679092348517/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-17725330760466229597996368198440000000000000)
      constant := (233844366818479844969997846202684320068030304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree044.table
  base := (-4015733219519506859884707830889282112601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1285444315050563115918613731918480000000000000)
      constant := (17086581103624386520766251962420420729277518076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12950559004236347343/4000000000000000000)
  centralHi := (40470496888238585447/12500000000000000000)
  directionLo := (327507035584314572561/100000000000000000000)
  directionHi := (163753517792157286281/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree045.table
  base := (-1556418944019921331634013260677182481121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-72410132181373123187728690878800000000000000)
      constant := (977091070828465842710403068598820519496018555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree045.table
  base := (-7782549151185177577337241938044909716161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-437604145462214165784170516283300000000000000)
      constant := (5949514963631724090613993021604434016622002106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327507035584314572561/100000000000000000000)
  centralHi := (163753517792157286281/50000000000000000000)
  directionLo := (66241559504006704983/20000000000000000000)
  directionHi := (82801949380008381229/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree046.table
  base := (-7509467658275424206418597444496743916593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-73918941320881327983471908963840000000000000)
      constant := (1019723995333151101976347767518226692688246063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree046.table
  base := (-3754925860469055823073974698214249679319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1340180557722721878786409365781320000000000000)
      constant := (18627297649039269111661542678174945008501835844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66241559504006704983/20000000000000000000)
  centralHi := (82801949380008381229/25000000000000000000)
  directionLo := (334867663292408034623/100000000000000000000)
  directionHi := (5232307238943875541/1562500000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree047.table
  base := (-288523530344882635919650543663566620139/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (1188)
      previous := (0)
      next := (880)
      square := (27940909990892681402652186760000000000000)
      linear := (-1604845754476373037855641001040000000000000)
      constant := (22622896839346070182363273491235309221336675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree047.table
  base := (-3606706351090173162712986161715266434781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8460000000000000000000000000000000000000000
      center := (21549)
      previous := (0)
      next := (15675)
      square := (502936379836068265247739361680000000000000)
      linear := (-29096780405506409791921429419420000000000000)
      constant := (413251869044195741840233635029904019192350548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334867663292408034623/100000000000000000000)
  centralHi := (5232307238943875541/1562500000000000000)
  directionLo := (338487959460545056151/100000000000000000000)
  directionHi := (42310994932568132019/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree048.table
  base := (-3446494992869759495391375193165536558553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-38468279799948868787479172566960000000000000)
      constant := (553873732626753530320945983862937329742156423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree048.table
  base := (-6893263945834968130809765987953805153247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-464972266798293547218068333214720000000000000)
      constant := (6745054737517520256765159103700940266498864262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338487959460545056151/100000000000000000000)
  centralHi := (42310994932568132019/12500000000000000000)
  directionLo := (171034971190550404409/50000000000000000000)
  directionHi := (342069942381100808819/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree049.table
  base := (-6549200531956384600276324811441170142549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-78445368739405942370701563218960000000000000)
      constant := (1153137875573522508324699571666846455155109259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree049.table
  base := (-3274715883626633018797158957829031294109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1422284921730960023088102816575580000000000000)
      constant := (21064275705114353870839352778271657865367275884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171034971190550404409/50000000000000000000)
  centralHi := (342069942381100808819/100000000000000000000)
  directionLo := (172807401650982285973/50000000000000000000)
  directionHi := (345614803301964571947/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree050.table
  base := (-1236348562956477789025688155314707072671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-79954177878914147166444781304000000000000000)
      constant := (1199447331784532656402484559224549060382348805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree050.table
  base := (-1236387582010215380324304099090331391591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1449653043067039404522000633507000000000000000)
      constant := (21910171458192926263060621922744226216037793290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172807401650982285973/50000000000000000000)
  centralHi := (345614803301964571947/100000000000000000000)
  directionLo := (87280918247597830499/25000000000000000000)
  directionHi := (349123672990391321997/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree051.table
  base := (-361914737612555523300141998638054674513/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-20365746754605587990546999847260000000000000)
      constant := (311668947996786467675925194925864148896003132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree051.table
  base := (-5790800341934112283419364384224809931711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-492340388134372928651966150146140000000000000)
      constant := (7590950252452121147963190260007085619165102406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87280918247597830499/25000000000000000000)
  centralHi := (349123672990391321997/100000000000000000000)
  directionLo := (88149406486639109201/25000000000000000000)
  directionHi := (70519525189311287361/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree052.table
  base := (-215035807715737438456961686808961198751/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-82971796157930556757931217474080000000000000)
      constant := (1294823221500323800478767404831255117798976025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree052.table
  base := (-2688016955918146834020724206239287658507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1504389285739198167389796267369840000000000000)
      constant := (23652313012181354827237498153404366888244889332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88149406486639109201/25000000000000000000)
  centralHi := (70519525189311287361/20000000000000000000)
  directionLo := (356037684247038325903/100000000000000000000)
  directionHi := (22252355265439895369/6250000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree053.table
  base := (-4937533984501638796242741344120490279163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-84480605297438761553674435559120000000000000)
      constant := (1343889591614926935676369415716717836973328933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree053.table
  base := (-4937650892568667471718565032851828444841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1531757407075277548823694084301260000000000000)
      constant := (24548557734676387585502235273391729347376232158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356037684247038325903/100000000000000000000)
  centralHi := (22252355265439895369/6250000000000000000)
  directionLo := (359444821057196200063/100000000000000000000)
  directionHi := (2808162664509345313/781250000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree054.table
  base := (-895112587269343597920320793412534154821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-85989414436946966349417653644160000000000000)
      constant := (1393874878562731098859340607421878560260002055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree054.table
  base := (-4475661428948159131824456644441792168677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-519708509470452310085863967077560000000000000)
      constant := (8487194840487750376480975798236813486596355042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359444821057196200063/100000000000000000000)
  centralHi := (2808162664509345313/781250000000000000)
  directionLo := (45352495480831494203/12500000000000000000)
  directionHi := (2902559710773215629/800000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree055.table
  base := (-1994995478743526153225541515410785419643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-43749111788227585572580435864600000000000000)
      constant := (722389531331813165667952714643957575008008613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree055.table
  base := (-3990073907887451206093117653457887665269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1586493649747436311691489718164100000000000000)
      constant := (26391393039061523375198955431780801220653574022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45352495480831494203/12500000000000000000)
  centralHi := (2902559710773215629/800000000000000000)
  directionLo := (366163997337984970543/100000000000000000000)
  directionHi := (22885249833624060659/6250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree056.table
  base := (-3480825425668760415182726283680562315083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-89007032715963375940904089814240000000000000)
      constant := (1496602127620171456967586952338869637845981653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree056.table
  base := (-1740447632024831494410366058095754857549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1613861771083515693125387535095520000000000000)
      constant := (27337983011735129373390514514156553190708273324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366163997337984970543/100000000000000000000)
  centralHi := (22885249833624060659/6250000000000000000)
  directionLo := (92369441553801323477/25000000000000000000)
  directionHi := (369477766215205293909/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree057.table
  base := (-1474036225753488741369038440628006449961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-45257920927735790368323653949640000000000000)
      constant := (774672029967008821085305653871992733752036151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree057.table
  base := (-2948131232297196482851794537024300166717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-547076630806531691519761784008980000000000000)
      constant := (9433784737151490098526833950451491175590332882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92369441553801323477/25000000000000000000)
  centralHi := (369477766215205293909/100000000000000000000)
  directionLo := (186381038807749923699/50000000000000000000)
  directionHi := (372762077615499847399/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree058.table
  base := (-478347419407508090717587075953322908861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-92024650994979785532390525984320000000000000)
      constant := (1603004848423127723134642497074575548471630255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree058.table
  base := (-1195893278102433999443336802051805551219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1668598013755674455993183168958360000000000000)
      constant := (29281506449605524295622849383596447215344860244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186381038807749923699/50000000000000000000)
  centralHi := (372762077615499847399/100000000000000000000)
  directionLo := (376017703425078067559/100000000000000000000)
  directionHi := (9400442585626951689/2500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree059.table
  base := (-1811823556527370022203188444500117254357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-93533460134487990328133744069360000000000000)
      constant := (1657584483822366072045594331687019240985125387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree059.table
  base := (-1811865160290551783812785799101173528117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1695966135091753837427080985889780000000000000)
      constant := (30278439570141611657712819656738242888175011846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376017703425078067559/100000000000000000000)
  centralHi := (9400442585626951689/2500000000000000000)
  directionLo := (75849076479523730639/20000000000000000000)
  directionHi := (94811345599404663299/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree060.table
  base := (-604167653033352383017357074660152288207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-47521134636998097561938481077200000000000000)
      constant := (856541479226524675942938910958075723595350737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree060.table
  base := (-37761571633815061036202882485644835791/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-574444752142611072953659600940400000000000000)
      constant := (10430717814642192747249591325341628427085634752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75849076479523730639/20000000000000000000)
  centralHi := (94811345599404663299/25000000000000000000)
  directionLo := (38244582211178884063/10000000000000000000)
  directionHi := (382445822111788840631/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree061.table
  base := (-116255045467555430819442289986936942129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-96551078413504399919620180239440000000000000)
      constant := (1769500265949541511131439497768814281474185195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree061.table
  base := (-290652320318836756709101586211554008607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1750702377763912600294876619752620000000000000)
      constant := (32322647964061948502642481601215116129019536932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38244582211178884063/10000000000000000000)
  centralHi := (382445822111788840631/100000000000000000000)
  directionLo := (77123940156506025857/20000000000000000000)
  directionHi := (192809850391265064643/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree062.table
  base := (69354289978545866947773781163186217329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-98059887553012604715363398324480000000000000)
      constant := (1826836401033037514697104004412669478354079761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree062.table
  base := (69329568372117240663539758123541363533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1778070499099991981728774436684040000000000000)
      constant := (33369923042026752581002310067455123251696799146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77123940156506025857/20000000000000000000)
  centralHi := (192809850391265064643/50000000000000000000)
  directionLo := (48595958617405576829/12500000000000000000)
  directionHi := (388767668939244614633/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree063.table
  base := (371775631734062595081275284980722629551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-49784348346260404755553308204760000000000000)
      constant := (942545679662192264647822991243062416288678159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree063.table
  base := (743530490463474789702812663738613540859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-601812873478690454387557417871820000000000000)
      constant := (11477992868162859134715505264365302833870545186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48595958617405576829/12500000000000000000)
  centralHi := (388767668939244614633/100000000000000000000)
  directionLo := (195945175491322148429/50000000000000000000)
  directionHi := (391890350982644296859/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree064.table
  base := (1441314047868818697785569762690702218623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-101077505832029014306849834494560000000000000)
      constant := (1944265137189198482988930169908503761200938207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree064.table
  base := (720648298540856952438519197189425065391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1832806741772150744596570070546880000000000000)
      constant := (35514814590669031578006655465497451838900153884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195945175491322148429/50000000000000000000)
  centralHi := (391890350982644296859/100000000000000000000)
  directionLo := (394988346630816653653/100000000000000000000)
  directionHi := (197494173315408326827/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree065.table
  base := (135165079815693555542427377171149109339/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-25646578742884304775648263144900000000000000)
      constant := (501089432902424811277235684856434273530119404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree065.table
  base := (2162626620660872193013130917207040027647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1860174863108230126030467887478300000000000000)
      constant := (36612430950167157305905380837822080075579300014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394988346630816653653/100000000000000000000)
  centralHi := (197494173315408326827/50000000000000000000)
  directionLo := (199031116131995930941/50000000000000000000)
  directionHi := (398062232263991861883/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree066.table
  base := (1453765908002855584156918342673972372993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-52047562055522711949168135332320000000000000)
      constant := (1032684570039325692755185096613926804971941537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree066.table
  base := (2907519509396844500268520329027072490931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-629180994814769835821455234803240000000000000)
      constant := (12575609213720373252905201215192969818794799474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199031116131995930941/50000000000000000000)
  centralHi := (398062232263991861883/100000000000000000000)
  directionLo := (401112562176551929433/100000000000000000000)
  directionHi := (200556281088275964717/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree067.table
  base := (1837992360555464340127702413776728892313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-52801966625276814347039744374840000000000000)
      constant := (1063649680255797248156673630457772794123119417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree067.table
  base := (1837987194939609895547537753377693983687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1914911105780388888898263521341140000000000000)
      constant := (38858004628922374172841859099051891486358724988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (401112562176551929433/100000000000000000000)
  centralHi := (200556281088275964717/50000000000000000000)
  directionLo := (10103496743599597441/2500000000000000000)
  directionHi := (404139869743983897641/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree068.table
  base := (893599841450052686248116899171664448743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-107112742390061833489822706834720000000000000)
      constant := (2190148391174206259958756068343031033836366435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree068.table
  base := (279249408513439142997492411393569928863/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1942279227116468270332161338272560000000000000)
      constant := (40005961884587964204465883317969838040183209696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10103496743599597441/2500000000000000000)
  centralHi := (404139869743983897641/100000000000000000000)
  directionLo := (203572334255867332797/50000000000000000000)
  directionHi := (81428933702346933119/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree069.table
  base := (5283574620598458264455599538033809299779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-108621551529570038285565924919760000000000000)
      constant := (2253916230622186683387194983990036684743211811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree069.table
  base := (1056713468903091934406305589620017890063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-656549116150849217255353051734660000000000000)
      constant := (13723566461382021072087434037204419835574475010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203572334255867332797/50000000000000000000)
  centralHi := (81428933702346933119/20000000000000000000)
  directionLo := (205063726606131111743/50000000000000000000)
  directionHi := (410127453212262223487/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree070.table
  base := (3061355208048817147148238048343868960437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-55065180334539121540654571502400000000000000)
      constant := (1159301438825751456070182414802791606533605333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree070.table
  base := (3061352155906555509461716110303345523597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-1997015469788627033199956972135400000000000000)
      constant := (42352217107597681094579655833389138249418527828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205063726606131111743/50000000000000000000)
  centralHi := (410127453212262223487/100000000000000000000)
  directionLo := (206544350357993557199/50000000000000000000)
  directionHi := (413088700715987114399/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree071.table
  base := (218293941837950151673957168793308611547/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-27909792452146611969263090272460000000000000)
      constant := (596052082814301773767607087357945349783258584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree071.table
  base := (109146890916241365579534681927406318949/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2024383591124706414633854789066820000000000000)
      constant := (43550515038263910032993837411516995673459208832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206544350357993557199/50000000000000000000)
  centralHi := (413088700715987114399/100000000000000000000)
  directionLo := (208014435460660041557/50000000000000000000)
  directionHi := (83205774184264016623/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree072.table
  base := (3935830704254226165596823231278108657613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-56573989474047326336397789587440000000000000)
      constant := (1225366295299674185287263291587333342024667117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree072.table
  base := (983957139328286231944441743014901451847/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-683917237486928598689250868666080000000000000)
      constant := (14921864387404470166685374989300236030742241104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208014435460660041557/50000000000000000000)
  centralHi := (83205774184264016623/20000000000000000000)
  directionLo := (104737101897117396599/25000000000000000000)
  directionHi := (418948407588469586397/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree073.table
  base := (1097684488357329281178619690480382315943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-28664197021900714367134699314980000000000000)
      constant := (629543913743688833729828235060612329071836174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree073.table
  base := (8781472306605701998585917931344814799919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2079119833796865177501650422929660000000000000)
      constant := (45997451467789239008799364777689566276074379278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104737101897117396599/25000000000000000000)
  centralHi := (418948407588469586397/100000000000000000000)
  directionLo := (52730967390163698941/12500000000000000000)
  directionHi := (421847739121309591529/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree074.table
  base := (9714849366888291819592532043750625254689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-116165597227111062264282015344960000000000000)
      constant := (2586537523793676548840593233168965131187608001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree074.table
  base := (9714846348774110296776269209550022150129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2106487955132944558935548239861080000000000000)
      constant := (47246089945217753868547351159434462980733429298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52730967390163698941/12500000000000000000)
  centralHi := (421847739121309591529/100000000000000000000)
  directionLo := (106181819825302046833/25000000000000000000)
  directionHi := (424727279301208187333/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree075.table
  base := (10671781564210530247834542327127544099077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-117674406366619267060025233430000000000000000)
      constant := (2655818196560441361738753192575624744914861093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree075.table
  base := (2667944758640494779418167057577147726233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-711285358823007980123148685597500000000000000)
      constant := (16170502862095112401160817121350291313853968728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106181819825302046833/25000000000000000000)
  centralHi := (424727279301208187333/100000000000000000000)
  directionLo := (213793713988188005511/50000000000000000000)
  directionHi := (427587427976376011023/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree076.table
  base := (11652272309779678533160840359195245351927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-119183215506127471855768451515040000000000000)
      constant := (2726017672857447886372596745497782296982406743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree076.table
  base := (728266886869545552899628442111520257061/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2161224197805103321803343873723920000000000000)
      constant := (49793707384071151294957764687006272295380151712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213793713988188005511/50000000000000000000)
  centralHi := (427587427976376011023/100000000000000000000)
  directionLo := (17217142868399440753/4000000000000000000)
  directionHi := (215214285854993009413/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree077.table
  base := (6328160721944638591039593183636821764153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-60346012322817838325755834800040000000000000)
      constant := (1398567976165952276860499767138793739277013977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree077.table
  base := (6328159833863050700203534659187854010169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2188592319141182703237241690655340000000000000)
      constant := (51092686332726195681095599651216938652304679556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17217142868399440753/4000000000000000000)
  centralHi := (215214285854993009413/50000000000000000000)
  directionLo := (216625542195019451053/50000000000000000000)
  directionHi := (433251084390038902107/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree078.table
  base := (3420982207800434217390170037560857184173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-30550208446285970361813721921280000000000000)
      constant := (717293258671212657241243179592691933519838157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree078.table
  base := (6841963671631866223804537767160836150631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-738653480159087361557046502528920000000000000)
      constant := (17469481809096874506440963755574904444680926548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216625542195019451053/50000000000000000000)
  centralHi := (433251084390038902107/100000000000000000000)
  directionLo := (54506915975462268101/12500000000000000000)
  directionHi := (436055327803698144809/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree079.table
  base := (14735094356631873895477732935925544393313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-123709642924652086242998105770160000000000000)
      constant := (2942128919662062941310934454179579527564828417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree079.table
  base := (3683773277587460817054598350065428611549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2243328561813341466105037324518180000000000000)
      constant := (53740984663542673496183680360591660039809645352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54506915975462268101/12500000000000000000)
  centralHi := (436055327803698144809/100000000000000000000)
  directionLo := (27427603261162025463/6250000000000000000)
  directionHi := (438841652178592407409/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree080.table
  base := (3952454480484298645766394565343326357133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-31304613016040072759685330963800000000000000)
      constant := (754000901761630955556727843146843407922906797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree080.table
  base := (15809816878229005403636163148883479470507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2270696683149420847538935141449600000000000000)
      constant := (55090304037873728265307159070749904910706299334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27427603261162025463/6250000000000000000)
  centralHi := (438841652178592407409/100000000000000000000)
  directionLo := (22080519834668901661/5000000000000000000)
  directionHi := (441610396693378033221/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree081.table
  base := (16908099442893175052746831083798414485139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-126727261203668495834484541940240000000000000)
      constant := (3090797096652181298462917030034630697597672051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree081.table
  base := (4227024642241730422531183359452532914717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-766021601495166742990944319460340000000000000)
      constant := (18818801182394988100956263634841286735006636472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22080519834668901661/5000000000000000000)
  centralHi := (441610396693378033221/100000000000000000000)
  directionLo := (694315453061982399/156250000000000000)
  directionHi := (444361889959668735361/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree082.table
  base := (3605987769390555750463779640598383656381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-128236070343176700630227760025280000000000000)
      constant := (3166509388318778966275135898142089147484728145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree082.table
  base := (360598762305999729621673739506422786521/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2325432925821579610406730775312440000000000000)
      constant := (57839283188801846121148450069560134141882400100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (694315453061982399/156250000000000000)
  centralHi := (444361889959668735361/100000000000000000000)
  directionLo := (447096450477270933053/100000000000000000000)
  directionHi := (223548225238635466527/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree083.table
  base := (9587668035653413782640180779174498773517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-64872439741342452712985489055160000000000000)
      constant := (1621570240953785675602108172206936467790699053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree083.table
  base := (4793833864713940350246185773762846932961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2352801047157658991840628592243860000000000000)
      constant := (59238942960403368825458381070002717028993581128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447096450477270933053/100000000000000000000)
  centralHi := (223548225238635466527/50000000000000000000)
  directionLo := (112453596766127497951/25000000000000000000)
  directionHi := (89962877412901998361/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree084.table
  base := (20344291061276218533999299141409503942019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-131253688622193110221714196195360000000000000)
      constant := (3320690377297772314816749453133293594207919971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree084.table
  base := (20344290548680030148656913334297362258079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-793389722831246124424842136391760000000000000)
      constant := (20218460953321163622410474354199197239368579066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112453596766127497951/25000000000000000000)
  centralHi := (89962877412901998361/20000000000000000000)
  directionLo := (226257999632646606531/50000000000000000000)
  directionHi := (452515999265293213063/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree085.table
  base := (21536803768978874518866416953296662127359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-132762497761701315017457414280400000000000000)
      constant := (3399159074383610348711338293856832326639336031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree085.table
  base := (21536803340017271692133369004768446320863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2407537289829817754708424226106700000000000000)
      constant := (62088602885702643219194511005040946712610154606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226257999632646606531/50000000000000000000)
  centralHi := (452515999265293213063/100000000000000000000)
  directionLo := (227600788867214211181/50000000000000000000)
  directionHi := (455201577734428422363/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree086.table
  base := (5688218538056040359926059848465753267987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-33567826725302379953300158091360000000000000)
      constant := (869636643267971585551217705745940848968983283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree086.table
  base := (2275287379330062455779615737214899137521/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2434905411165897136142322043038120000000000000)
      constant := (63538603036047568335433647860710923195061100020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227600788867214211181/50000000000000000000)
  centralHi := (455201577734428422363/100000000000000000000)
  directionLo := (457871404602601182737/100000000000000000000)
  directionHi := (228935702301300591369/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree087.table
  base := (4798500434719130238433724260056457080393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-135780116040717724608943850450480000000000000)
      constant := (3558852873279947405614850823849403568452940685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree087.table
  base := (959700074932601742608793742473144077977/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-820757844167325505858739953323180000000000000)
      constant := (21668461103199348529828252496041087540237678950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457871404602601182737/100000000000000000000)
  centralHi := (228935702301300591369/50000000000000000000)
  directionLo := (230262876911153955473/50000000000000000000)
  directionHi := (460525753822307910947/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree088.table
  base := (6313921949922462713655736158475911736273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-34322231295056482351171767133880000000000000)
      constant := (910019493733501305769345751801593289025427057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree088.table
  base := (25255687548503653296064426526954122466283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2489641653838055899010117676900960000000000000)
      constant := (66488943705099310500963804765652989817504344646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230262876911153955473/50000000000000000000)
  centralHi := (460525753822307910947/100000000000000000000)
  directionLo := (92632978299189103283/20000000000000000000)
  directionHi := (3618475714812074347/781250000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree089.table
  base := (13271215500242048893613101730910388631087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-69398867159867067100215143310280000000000000)
      constant := (1861110938983869866410529295474441048486071183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree089.table
  base := (1327121539519625514196439356658148721551/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2517009775174135280444015493832380000000000000)
      constant := (67989284221419182129759748394279579939326217240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92632978299189103283/20000000000000000000)
  centralHi := (3618475714812074347/781250000000000000)
  directionLo := (46578907618716974077/10000000000000000000)
  directionHi := (465789076187169740771/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree090.table
  base := (5570546349762287445460209380025060942737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-140306543459242338996173504705600000000000000)
      constant := (3805284582321139131775123306974376798112530165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree090.table
  base := (1392636578655664438155113464762657163899/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-848125965503404887292637770254600000000000000)
      constant := (23168801619176361368925467088914410161006346920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46578907618716974077/10000000000000000000)
  centralHi := (465789076187169740771/100000000000000000000)
  directionLo := (468398559216553367009/100000000000000000000)
  directionHi := (46839855921655336701/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree091.table
  base := (7296647504981029986297983385006781594861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-35453838149687635947979180697660000000000000)
      constant := (972316521984883910472817016077709980543047949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree091.table
  base := (29186589873006960100082718003058473990483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2571746017846294043311811127695220000000000000)
      constant := (71040305612488286135488450695529714792809585046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468398559216553367009/100000000000000000000)
  centralHi := (46839855921655336701/10000000000000000000)
  directionLo := (235496792471250595723/50000000000000000000)
  directionHi := (470993584942501191447/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree092.table
  base := (30544005791130519749410367114232006202921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-143324161738258748587659940875680000000000000)
      constant := (3974166394772803460912494774703818501702252489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree092.table
  base := (1527200283414723684321945680401700570099/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2599114139182373424745708944626640000000000000)
      constant := (72590986485430809605603454524973588361365528760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235496792471250595723/50000000000000000000)
  centralHi := (470993584942501191447/100000000000000000000)
  directionLo := (23678719551415524069/5000000000000000000)
  directionHi := (473574391028310481381/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree093.table
  base := (31924979041492887733790853150726769630683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-144832970877766953383403158960720000000000000)
      constant := (4059985502774691101505083860864635434114178747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree093.table
  base := (31924978938802874437717118807390095696079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-875494086839484268726535587186020000000000000)
      constant := (24719482491851512492351121084147109578355831066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23678719551415524069/5000000000000000000)
  centralHi := (473574391028310481381/100000000000000000000)
  directionLo := (95228241739240602837/20000000000000000000)
  directionHi := (238070604348101507093/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree094.table
  base := (16664754875787763077657121245359079458969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235000000000000000000000000000000000000000
      center := (594)
      previous := (0)
      next := (440)
      square := (13970454995446340701326093380000000000000)
      linear := (-1556827446992288916799429543040000000000000)
      constant := (44114078850024096886752191726611876734571543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree094.table
  base := (33329509665737297801328037107344235230227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8460000000000000000000000000000000000000000
      center := (21549)
      previous := (0)
      next := (15675)
      square := (502936379836068265247739361680000000000000)
      linear := (-56464901741585791225819246350840000000000000)
      constant := (1611546565576854220116981303632918223004772042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95228241739240602837/20000000000000000000)
  centralHi := (238070604348101507093/50000000000000000000)
  directionLo := (19147770518763888163/4000000000000000000)
  directionHi := (119673565742274301019/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree095.table
  base := (17378798951617378756469818399753220102513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-73925294578391681487444797565400000000000000)
      constant := (2117190061057723047430780957296554863206451217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree095.table
  base := (8689399457872735147775109554649202462851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2681218503190611569047402395420900000000000000)
      constant := (77343709804403560502649188121127940103311525848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19147770518763888163/4000000000000000000)
  centralHi := (119673565742274301019/25000000000000000000)
  directionLo := (481233772900835816497/100000000000000000000)
  directionHi := (240616886450417908249/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree096.table
  base := (1448369739177741925561298316863018843923/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-149359398296291567770632813215840000000000000)
      constant := (4322955633376621346653846754593880215655647675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree096.table
  base := (18104621709743237783178761270092550154523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-902862208175563650160433404117440000000000000)
      constant := (26320503713923208754254257632616733319496095684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481233772900835816497/100000000000000000000)
  centralHi := (240616886450417908249/50000000000000000000)
  directionLo := (96751990359107187633/20000000000000000000)
  directionHi := (241879975897767969083/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree097.table
  base := (37684446464144873685524950259513912385279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-150868207435799772566376031300880000000000000)
      constant := (4412449945650320895946678870189146232459081311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree097.table
  base := (37684446414043509466942715043306971512033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2735954745862770331915198029283740000000000000)
      constant := (80596092593586861829028529864618705551261456146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96751990359107187633/20000000000000000000)
  centralHi := (241879975897767969083/50000000000000000000)
  directionLo := (97254601483336568853/20000000000000000000)
  directionHi := (243136503708341422133/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree098.table
  base := (39183206842128930368386618366658933114379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-152377016575307977362119249385920000000000000)
      constant := (4502863058902946286181134896937229583249663211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree098.table
  base := (783664136005352390376855475363081428751/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2763322867198849713349095846215160000000000000)
      constant := (82247454159263035163106144494627557188499863100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97254601483336568853/20000000000000000000)
  centralHi := (243136503708341422133/50000000000000000000)
  directionLo := (97754628437309570159/20000000000000000000)
  directionHi := (122193285546636962699/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree099.table
  base := (40705524598930137205090698150898151117193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-153885825714816182157862467470960000000000000)
      constant := (4594194973102543048966813212958654015817879337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree099.table
  base := (10176381140989319093403931954465369181861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-930230329511643031594331221048860000000000000)
      constant := (27971865279411155018347622380358537262545542776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97754628437309570159/20000000000000000000)
  centralHi := (122193285546636962699/25000000000000000000)
  directionLo := (245630276688235929421/50000000000000000000)
  directionHi := (491260553376471858843/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree100.table
  base := (21125699860370285464059644035846318876627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-77697317427162193476802842778000000000000000)
      constant := (2343222844109304740902883386875184518398469043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree100.table
  base := (42251399691525600242120193487030616471857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2818059109871008476216891480078000000000000000)
      constant := (85600517629957909990662858105068811372153978034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245630276688235929421/50000000000000000000)
  centralHi := (491260553376471858843/100000000000000000000)
  directionLo := (493735433288520817067/100000000000000000000)
  directionHi := (123433858322130204267/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree101.table
  base := (43820832194337051764841054075135127015593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-156903443993832591749348903641040000000000000)
      constant := (4779615204221935580580252962387293495577444937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree101.table
  base := (10955208042483606232846773774350775762361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2845427231207087857650789297009420000000000000)
      constant := (87302219533917946405801280999488245933451992328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493735433288520817067/100000000000000000000)
  centralHi := (123433858322130204267/25000000000000000000)
  directionLo := (248098984714493251427/50000000000000000000)
  directionHi := (99239593885797300571/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree102.table
  base := (11353455501754893878533269215946455296573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-39603063283335199136273030431520000000000000)
      constant := (1218425880271116759002497812535345719750129757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree102.table
  base := (22706910993319290423027702336486907941863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-957598450847722413028229037980280000000000000)
      constant := (29673567183204917755669130209983999955722904404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248098984714493251427/50000000000000000000)
  centralHi := (99239593885797300571/20000000000000000000)
  directionLo := (498648344674175628587/100000000000000000000)
  directionHi := (124662086168543907147/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree103.table
  base := (11757592286639795607970889844733187899663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-39980265568212250335208834952780000000000000)
      constant := (1242177659694797519005059669327485612070355567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree103.table
  base := (11757592282384667170105232438071436617521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2900163473879246620518584930872260000000000000)
      constant := (90755963676567234259087776895807619601143480008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (498648344674175628587/100000000000000000000)
  centralHi := (124662086168543907147/25000000000000000000)
  directionLo := (501086737428902115097/100000000000000000000)
  directionHi := (250543368714451057549/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree104.table
  base := (48670473601153680520007110910897687187633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-161429871412357206136578557896160000000000000)
      constant := (5064636557280033658487224615815292990997481297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree104.table
  base := (24335236793470446823845176936901819511581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2927531595215326001952482747803680000000000000)
      constant := (92508005914310420713729963947911540294838967444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501086737428902115097/100000000000000000000)
  centralHi := (250543368714451057549/50000000000000000000)
  directionLo := (251756660889035628003/50000000000000000000)
  directionHi := (503513321778071256007/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree105.table
  base := (50334135359389911614647711556760645498901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-162938680551865410932321775981200000000000000)
      constant := (5161481276561786117026991117691884265907072309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree105.table
  base := (25167067673761388264894111823720778312453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-984966572183801794462126854911700000000000000)
      constant := (31425609420798036070754945202855721641506504124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251756660889035628003/50000000000000000000)
  centralHi := (503513321778071256007/100000000000000000000)
  directionLo := (15810258363491258049/3125000000000000000)
  directionHi := (505928267631720257569/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree106.table
  base := (52021354410211472886448832567821886046831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-164447489691373615728064994066240000000000000)
      constant := (5259244796600023857789489610933838546277449679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree106.table
  base := (52021354400303761557577561272016891451331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-2982267837887484764820278381666520000000000000)
      constant := (96062430720381687896199967366443870637887823222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15810258363491258049/3125000000000000000)
  centralHi := (505928267631720257569/100000000000000000000)
  directionLo := (254165870431928563439/50000000000000000000)
  directionHi := (508331740863857126879/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree107.table
  base := (53732130742890992024943082118472926963947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-165956298830881820523808212151280000000000000)
      constant := (5357927117371050115340897626998386695663358923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree107.table
  base := (13433032683654977390576321447868511277599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3009635959223564146254176198597940000000000000)
      constant := (97864813287849140216307399216566974731679565752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254165870431928563439/50000000000000000000)
  centralHi := (508331740863857126879/100000000000000000000)
  directionLo := (255361951722709479433/50000000000000000000)
  directionHi := (510723903445418958867/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree108.table
  base := (27733232173503104061274411092670002811663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-83732553985195012659775715118160000000000000)
      constant := (2728764119425921057668183663745948036210963567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree108.table
  base := (3466654021256375256322987206999752420763/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-1012334693519881175896024671843120000000000000)
      constant := (33227991988128054796129458113478175497356684832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255361951722709479433/50000000000000000000)
  centralHi := (510723903445418958867/100000000000000000000)
  directionLo := (513104913571651213227/100000000000000000000)
  directionHi := (128276228392912803307/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree109.table
  base := (22889742084967695039472188950101859511/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-42243479277474557528823662080340000000000000)
      constant := (1389512040255001318236596291331464379787374375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree109.table
  base := (57224355206656513415598817692685581905077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3064372201895722909121971832460780000000000000)
      constant := (101519918749585421402658780625180167857709671674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513104913571651213227/100000000000000000000)
  centralHi := (128276228392912803307/25000000000000000000)
  directionLo := (103094985156838292313/20000000000000000000)
  directionHi := (257737462892095730783/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree110.table
  base := (3776371413072544637496667397841273611/640000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-170482726249406434911037866406400000000000000)
      constant := (5659486883853733288953123336945615209479671875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree110.table
  base := (59005803324448946313429800175496762761617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3091740323231802290555869649392200000000000000)
      constant := (103372641643061872220335612076038477280927415154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103094985156838292313/20000000000000000000)
  centralHi := (257737462892095730783/50000000000000000000)
  directionLo := (10356681821762484351/2000000000000000000)
  directionHi := (517834091088124217551/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree111.table
  base := (60810808687902945553336389733006425216693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-171991535388914639706781084491440000000000000)
      constant := (5761844407331773198396859337533931193303674837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree111.table
  base := (30405404341944609416074442154480180373409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-1039702814855960557329922488774540000000000000)
      constant := (35080714881477398640967157392420711871338325772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10356681821762484351/2000000000000000000)
  centralHi := (517834091088124217551/100000000000000000000)
  directionLo := (260091278532128871483/50000000000000000000)
  directionHi := (520182557064257742967/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree112.table
  base := (62639371278968019810097436512147926324153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-173500344528422844502524302576480000000000000)
      constant := (5865120731433394586511440718069414769250053977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree112.table
  base := (6263937127561871369648698424134944906187/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3146476565903961053423665283255040000000000000)
      constant := (107128427753324275170257111537214776793598074940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260091278532128871483/50000000000000000000)
  centralHi := (520182557064257742967/100000000000000000000)
  directionLo := (522520467976859062477/100000000000000000000)
  directionHi := (261260233988429531239/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree113.table
  base := (322457455466467092454608339697992616119/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-43752288416982762324566880165380000000000000)
      constant := (1492328964034590579785040518842913284450343550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree113.table
  base := (201535909657808651530863578472936960339/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3173844687240040434857563100186460000000000000)
      constant := (109031490969374738467394963087100427963439781760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (522520467976859062477/100000000000000000000)
  centralHi := (261260233988429531239/50000000000000000000)
  directionLo := (524847964877069739499/100000000000000000000)
  directionHi := (1049695929754139479/200000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree114.table
  base := (33183584060966019033004930688174164689431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-88258981403719627047005369373280000000000000)
      constant := (3037214890713456122292848463315536729798953079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree114.table
  base := (829589601495004663331304448230819540849/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-1067070936192039938763820305705960000000000000)
      constant := (36983778097409516837632408595310947575553011680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524847964877069739499/100000000000000000000)
  centralHi := (1049695929754139479/200000000000000000)
  directionLo := (527165185702212191139/100000000000000000000)
  directionHi := (26358259285110609557/5000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree115.table
  base := (68266402356140126600369706713086502487561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-178026771946947458889753956831600000000000000)
      constant := (6180462507279729414823647258816208083995022249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree115.table
  base := (34133201177097446825307931014864744260757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3228580929912199197725358734049300000000000000)
      constant := (112887957721538643370572323182351947672592439668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527165185702212191139/100000000000000000000)
  centralHi := (26358259285110609557/5000000000000000000)
  directionLo := (529472265371184384473/100000000000000000000)
  directionHi := (264736132685592192237/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree116.table
  base := (7018919378736839463092825798507942099293/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-89767790543227831842748587458320000000000000)
      constant := (3143707016838964224715042467145480220486691185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree116.table
  base := (70189193785745671634485217150181332009583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3255949051248278579159256550980720000000000000)
      constant := (114841361256965582420859868121220770123365039246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529472265371184384473/100000000000000000000)
  centralHi := (264736132685592192237/50000000000000000000)
  directionLo := (531769335876129597461/100000000000000000000)
  directionHi := (265884667938064798731/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree117.table
  base := (36067771203626976920564617806878902276049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-90522195112981934240620196500840000000000000)
      constant := (3197642180301517864056868565733135495127792241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree117.table
  base := (18033885601475092599231553603161893882003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-1094439057528119320197718122637380000000000000)
      constant := (38937181632725754018342751549157492216048271048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531769335876129597461/100000000000000000000)
  centralHi := (265884667938064798731/50000000000000000000)
  directionLo := (106811305274111497771/20000000000000000000)
  directionHi := (66757065796319686107/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree118.table
  base := (18526362051903241205157082028723534533613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-45638299841368018319245902771680000000000000)
      constant := (1626018372009243287404288316568370287784751117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree118.table
  base := (2964217928259358577205429341105324033403/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3310685293920437342027052184843560000000000000)
      constant := (118798508644848626908836215092156162355404252150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106811305274111497771/20000000000000000000)
  centralHi := (66757065796319686107/12500000000000000000)
  directionLo := (536333963254082950307/100000000000000000000)
  directionHi := (134083490813520737577/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree119.table
  base := (15219782236086778936300820643219007017977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-184062008504980278072726829171760000000000000)
      constant := (6613781415962043237790914894822873932513555965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree119.table
  base := (3804945558974614121799354535119318399459/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3338053415256516723460950001774980000000000000)
      constant := (120802252496661415123127636254304440513985775160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536333963254082950307/100000000000000000000)
  centralHi := (134083490813520737577/25000000000000000000)
  directionLo := (538601770253940062469/100000000000000000000)
  directionHi := (53860177025394006247/10000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree120.table
  base := (39057965658935650736945658384956064207113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-92785408822244241434235023628400000000000000)
      constant := (3362204072180457705683884846396367945833512617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree120.table
  base := (39057965658543015227525883948092044630419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-1121807178864198701631615939568800000000000000)
      constant := (40940925484434640230495907133194023919063146852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538601770253940062469/100000000000000000000)
  centralHi := (53860177025394006247/10000000000000000000)
  directionLo := (135215017125854975291/25000000000000000000)
  directionHi := (108172013700683980233/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree121.table
  base := (10019563576530009471456893718006103909723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-46769906695999171916053316335460000000000000)
      constant := (1708988418304153315906346461235180967073156214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree121.table
  base := (10019563576448154129536603505839693005561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3392789657928675486328745635637820000000000000)
      constant := (124860080514470772430032339836517536736296931856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135215017125854975291/25000000000000000000)
  centralHi := (108172013700683980233/20000000000000000000)
  directionLo := (543108976617372898773/100000000000000000000)
  directionHi := (271554488308686449387/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree122.table
  base := (41110321528005040476652126136248662563053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (27918)
      previous := (0)
      next := (20680)
      square := (656611384785978012962326388860000000000000)
      linear := (-94294217961752446229978241713440000000000000)
      constant := (3474209001256251361383444479706413295601784077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree122.table
  base := (82220643055464040367084434663986228229017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3420157779264754867762643452569240000000000000)
      constant := (126914164679862727498511863054595435406842173954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543108976617372898773/100000000000000000000)
  centralHi := (271554488308686449387/50000000000000000000)
  directionLo := (545348610764908922591/100000000000000000000)
  directionHi := (17042144086403403831/3125000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree123.table
  base := (84308334641801142974467810018242738537333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-190097245063013097255699701511920000000000000)
      constant := (7061801132232280984328263907338578209428968597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree123.table
  base := (21077083660336464378233121442964065588581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-1149175300200278083065513756500220000000000000)
      constant := (42995009649728825909713645523680244151244210296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545348610764908922591/100000000000000000000)
  centralHi := (17042144086403403831/3125000000000000000)
  directionLo := (66843149992605121/12207031250000000)
  directionHi := (547579084739421151233/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree124.table
  base := (10802447920297293517316789096197442069663/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-47901513550630325512860729899240000000000000)
      constant := (1794025765589991530988423965665080299063771134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree124.table
  base := (86419583361998758754089424596852625089857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3474894021936913630630439086432080000000000000)
      constant := (131072673322154467291450958033426514078822894034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66843149992605121/12207031250000000)
  centralHi := (547579084739421151233/100000000000000000000)
  directionLo := (549800510026053180463/100000000000000000000)
  directionHi := (34362531876628323779/6250000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree125.table
  base := (22138597302661903447149895410237301484781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-48278715835507376711796534420500000000000000)
      constant := (1822830948219971828263520873554964198979881229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree125.table
  base := (1771087784206623113840276215724374275269/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3502262143272993012064336903363500000000000000)
      constant := (133177097798484720447539122690446472246662298900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549800510026053180463/100000000000000000000)
  centralHi := (34362531876628323779/6250000000000000000)
  directionLo := (22080519834668901661/4000000000000000000)
  directionHi := (276006497933361270763/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree126.table
  base := (22678188044912875546968413078318118106077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-48655918120384427910732338941760000000000000)
      constant := (1851865830944168892917214442709084722896324093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree126.table
  base := (453563760896938462652963846327500064821/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-1176543421536357464499411573431640000000000000)
      constant := (45099434125966892780080130134463382171827506800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22080519834668901661/4000000000000000000)
  centralHi := (276006497933361270763/50000000000000000000)
  directionLo := (554216649322807940863/100000000000000000000)
  directionHi := (2164908786417218519/390625000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree127.table
  base := (18578934452513050462062721821448871444933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (55836)
      previous := (0)
      next := (41360)
      square := (1313222769571956025924652777720000000000000)
      linear := (-196132481621045916438672573852080000000000000)
      constant := (7524521655035255002691489891774182785109284985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree127.table
  base := (1161183403279316823489590964284048232759/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3556998385945151774932132537226340000000000000)
      constant := (137436287060131043913495377104026919816477068640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554216649322807940863/100000000000000000000)
  centralHi := (2164908786417218519/390625000000000000)
  directionLo := (556411575335602005049/100000000000000000000)
  directionHi := (11128231506712040101/2000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree128.table
  base := (2971879670396656499380212657796384863693/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-49410322690138530308603947984280000000000000)
      constant := (1910624696660208614957435564967297713311182696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree128.table
  base := (47550074726254854856118697037802237979233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 397620000000000000000000000000000000000000000
      center := (1012803)
      previous := (0)
      next := (736725)
      square := (23638009852295208466643749998960000000000000)
      linear := (-3584366507281231156366030354157760000000000000)
      constant := (139591051844909634194918154164466825173060525092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell169.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556411575335602005049/100000000000000000000)
  centralHi := (11128231506712040101/2000000000000000000)
  directionLo := (279298938392313057597/50000000000000000000)
  directionHi := (111719575356925223039/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree129.table
  base := (1520768495991628498499248545586993920021/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (13959)
      previous := (0)
      next := (10340)
      square := (328305692392989006481163194430000000000000)
      linear := (-49787524975015581507539752505540000000000000)
      constant := (1940348679644724902132578652508256713109222224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree129.table
  base := (97329183743311448866379114398986843167133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132540000000000000000000000000000000000000000
      center := (337601)
      previous := (0)
      next := (245575)
      square := (7879336617431736155547916666320000000000000)
      linear := (-1203911542872436845933309390363060000000000000)
      constant := (47254198910658413093246885423817322869337180782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell169.Kernel129
