import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell021.Parameters
import ForestUnimodality.BinomialMassData.Q7_17.Batch000_049
import ForestUnimodality.BinomialMassData.Q7_17.Batch050_099
import ForestUnimodality.BinomialMassData.Q7_17.Batch100_149
import ForestUnimodality.BinomialMassData.Q64_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q64_153.Batch050_099
import ForestUnimodality.BinomialMassData.Q64_153.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree000.table
  base := (1777060293657514893460813741/100000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (430)
      previous := (301)
      next := (0)
      square := (8480053123527854785912438710000000000000)
      linear := (28296925436253977381717560900000000000000)
      constant := (3021002499217775318883383359700000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree000.table
  base := (1777060293657514893460813741/100000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3827)
      previous := (2752)
      next := (0)
      square := (76320478111750693073211948390000000000000)
      linear := (254672328926285796435458048100000000000000)
      constant := (27189022492959977869950450237300000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree001.table
  base := (113610498702042611861138206192174296210859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (362326988686927648486424393360000000000000)
      constant := (32659798152898470214697489810108371604938251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree001.table
  base := (56301233010012396172999893254583880131573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (9731948375805879380417983988460000000000000)
      constant := (873885097329197986963705333986396033333328238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24607647839237516117/50000000000000000000)
  directionHi := (9843059135695006447/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree002.table
  base := (74100160765049690376779731702038794907941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (243606244957537681483650251420000000000000)
      constant := (21116559529239537749547581196769211728394949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree002.table
  base := (36435320494789045336075899827043896578239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (6475607976371183142627607523820000000000000)
      constant := (560467850908977497980856035507887049999997834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24607647839237516117/50000000000000000000)
  centralHi := (9843059135695006447/20000000000000000000)
  directionLo := (34800469312350682603/50000000000000000000)
  directionHi := (69600938624701365207/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree003.table
  base := (49394138894036605108992322393486795031653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (124885501228147714480876109480000000000000)
      constant := (13900653260772644407987852714647683764147717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree003.table
  base := (48255315280066430278916687370395945288649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (1073089192312162301612410353060000000000000)
      constant := (122122259335807909333648846802079853695776049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34800469312350682603/50000000000000000000)
  centralHi := (69600938624701365207/100000000000000000000)
  directionLo := (17048678524928751263/20000000000000000000)
  directionHi := (21310848156160939079/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree004.table
  base := (33644158392389992376683440438553310385789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (6164757498757747478101967540000000000000)
      constant := (9321927960176528086182560931461906701493021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree004.table
  base := (32691433456828492140567434056371949492637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-37072822498209332953145405460000000000000)
      constant := (244256251067874404666228945941230321891046511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17048678524928751263/20000000000000000000)
  centralHi := (21310848156160939079/25000000000000000000)
  directionLo := (24607647839237516117/25000000000000000000)
  directionHi := (98430591356950064469/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree005.table
  base := (4669717169952084788047640158679722476081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-112555986230632219524672174400000000000000)
      constant := (6368411571860204022883004069542198977937045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree005.table
  base := (903453540643163363729475609991761671399/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-3293413221932905570743521870100000000000000)
      constant := (166102767489793673522047884859142908048159925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24607647839237516117/25000000000000000000)
  centralHi := (98430591356950064469/100000000000000000000)
  directionLo := (55024373334910902729/50000000000000000000)
  directionHi := (110048746669821805459/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree006.table
  base := (16415978852624881377167854276858671520973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-231276729960022186527446316340000000000000)
      constant := (4435677238315519893989933615532156069561197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree006.table
  base := (15816404410016582386167921393604533655913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-2183251207122533936177966111580000000000000)
      constant := (38445224407395154813748478737085392039029713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55024373334910902729/50000000000000000000)
  centralHi := (110048746669821805459/100000000000000000000)
  directionLo := (30138090488116465833/25000000000000000000)
  directionHi := (120552361952465863333/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree007.table
  base := (11586341181030626521000446255592305465027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-349997473689412153530220458280000000000000)
      constant := (3159586051976134369392954680396176279392803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree007.table
  base := (11115182446798133012643224043839364226869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-9806094020802298046324274799380000000000000)
      constant := (82072869122599987609406481224318559062258807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30138090488116465833/25000000000000000000)
  centralHi := (120552361952465863333/100000000000000000000)
  directionLo := (130211433065756796023/100000000000000000000)
  directionHi := (16276429133219599503/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree008.table
  base := (1619191344533587860795000904791265486261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-468718217418802120532994600220000000000000)
      constant := (2319424056384538349509146296703378627647145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree008.table
  base := (7722437632177241923630084212002305753011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-13062434420236994284114651264020000000000000)
      constant := (60382241530931849961928752646093991790744833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130211433065756796023/100000000000000000000)
  centralHi := (16276429133219599503/12500000000000000000)
  directionLo := (139201877249402730413/100000000000000000000)
  directionHi := (69600938624701365207/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree009.table
  base := (5478003907094473282359023847981713327387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-587438961148192087535768742160000000000000)
      constant := (1780279817682893712099814451836715151614843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree009.table
  base := (1294407861930322997664901150321721086979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-5439591606557230173968342576220000000000000)
      constant := (15556736129283780015123148289867186188929516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139201877249402730413/100000000000000000000)
  centralHi := (69600938624701365207/50000000000000000000)
  directionLo := (73822943517712548351/50000000000000000000)
  directionHi := (147645887035425096703/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree010.table
  base := (3443922186158387642056231927596509906779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-706159704877582054538542884100000000000000)
      constant := (1458759337455318461891136451075391363059131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree010.table
  base := (639672244938523745740719508900053952601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-19575115219106386759695404193300000000000000)
      constant := (38733181669198461883053609527735604960728015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73822943517712548351/50000000000000000000)
  centralHi := (147645887035425096703/100000000000000000000)
  directionLo := (155632430062622975911/100000000000000000000)
  directionHi := (19454053757827871989/12500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree011.table
  base := (453182995013113499831910913063917931339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-824880448606972021541317026040000000000000)
      constant := (1302559517137523595982545597471889128627884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree011.table
  base := (201087618575340586607233739490933122499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-22831455618541082997485780657940000000000000)
      constant := (35198410683919469912393827660542009238877576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155632430062622975911/100000000000000000000)
  centralHi := (19454053757827871989/12500000000000000000)
  directionLo := (163228669711901269961/100000000000000000000)
  directionHi := (81614334855950634981/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree012.table
  base := (468835694223595341632329220257608218353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-943601192336361988544091167980000000000000)
      constant := (1278272651903669857749713178334448775104017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree012.table
  base := (148430156030814494200490308011533998387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-8695932005991926411758719040860000000000000)
      constant := (11731198554483447737292898122755999859609174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163228669711901269961/100000000000000000000)
  centralHi := (81614334855950634981/50000000000000000000)
  directionLo := (170486785249287512631/100000000000000000000)
  directionHi := (21310848156160939079/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree013.table
  base := (-165813258060244494570923006656771182991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-1062321936065751955546865309920000000000000)
      constant := (1364083183449961039136238783434772512462404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree013.table
  base := (-809916698268927768380768125364612261699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-29344136417410475473066533587220000000000000)
      constant := (38151021435712643810390225950419930521962703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170486785249287512631/100000000000000000000)
  centralHi := (21310848156160939079/12500000000000000000)
  directionLo := (177448272105863012779/100000000000000000000)
  directionHi := (8872413605293150639/5000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree014.table
  base := (-817053229639633553253819000601327761899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-1181042679795141922549639451860000000000000)
      constant := (1545375728654314808922916435972432553622378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree014.table
  base := (-1760302600526647139422428520428634765229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-32600476816845171710856910051860000000000000)
      constant := (43690896341677886420149209995255362926918113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177448272105863012779/100000000000000000000)
  centralHi := (8872413605293150639/5000000000000000000)
  directionLo := (23018346827203717463/12500000000000000000)
  directionHi := (36829354923525947941/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree015.table
  base := (-495714970631611299598642091408927410517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-1299763423524531889552413593800000000000000)
      constant := (1812078560565630459628126329164099891802935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree015.table
  base := (-2587848921160524153941374813059060863019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-11952272405426622649549095505500000000000000)
      constant := (17183805940154854276057491759233382695287581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23018346827203717463/12500000000000000000)
  centralHi := (36829354923525947941/20000000000000000000)
  directionLo := (190610020541407653851/100000000000000000000)
  directionHi := (47652505135351913463/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree016.table
  base := (-3221390098745951600111287641030067261003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-1418484167253921856555187735740000000000000)
      constant := (2157044164456881016961684649662310561570133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree016.table
  base := (-3316406175501691213861821820359490110011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-39113157615714564186437662981140000000000000)
      constant := (61546480300943846902245373579894898671584167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190610020541407653851/100000000000000000000)
  centralHi := (47652505135351913463/25000000000000000000)
  directionLo := (24607647839237516117/12500000000000000000)
  directionHi := (196861182713900128937/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree017.table
  base := (-1940308760177911528090900721054587984423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (430)
      previous := (301)
      next := (0)
      square := (8480053123527854785912438710000000000000)
      linear := (-90423818293135989621056581040000000000000)
      constant := (151473627153038050882595945974144008529618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree017.table
  base := (-1981720028680192749787788412500912609117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (11481)
      previous := (8256)
      next := (0)
      square := (228961434335252079219635845170000000000000)
      linear := (-2492323412655838848484002320340000000000000)
      constant := (4325870527900850466104154863244162224830594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24607647839237516117/12500000000000000000)
  centralHi := (196861182713900128937/100000000000000000000)
  directionLo := (101459931239178471707/50000000000000000000)
  directionHi := (40583972495671388683/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree018.table
  base := (-2234905641122147714708400770035331250451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-1655925654712701790560736019620000000000000)
      constant := (3062183898529763504987183267399578537239322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree018.table
  base := (-567761441346188828364429159833582362419/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-15208612804861318887339471970140000000000000)
      constant := (29142944966075882992801655086662818202785448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101459931239178471707/50000000000000000000)
  centralHi := (40583972495671388683/20000000000000000000)
  directionLo := (10440140793705204781/5000000000000000000)
  directionHi := (208802815874104095621/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree019.table
  base := (-2499691823469851176292250293347487620599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-1774646398442091757563510161560000000000000)
      constant := (3615431731370542517040827750815152155293778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree019.table
  base := (-202499256614995572179811133105111370659/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-48882178814018652899808792375060000000000000)
      constant := (103134615316987065470834209932080399368695575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10440140793705204781/5000000000000000000)
  centralHi := (208802815874104095621/100000000000000000000)
  directionLo := (42904900067789338919/20000000000000000000)
  directionHi := (53631125084736673649/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree020.table
  base := (-5477493351328649487511703564894027826847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-1893367142171481724566284303500000000000000)
      constant := (4232437285163754864897117891745625958041217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree020.table
  base := (-1383139006776099317251849205847315967501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-52138519213453349137599168839700000000000000)
      constant := (120595135127407493027648467995093574022358788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42904900067789338919/20000000000000000000)
  centralHi := (53631125084736673649/25000000000000000000)
  directionLo := (55024373334910902729/25000000000000000000)
  directionHi := (220097493339643610917/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree021.table
  base := (-738829552685782931829107353390220812067/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-2012087885900871691569058445440000000000000)
      constant := (4911323208373688955250498116331809482501096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree021.table
  base := (-2979325173850582321624272718964115604497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-18464953204296015125129848434780000000000000)
      constant := (46586987488982429100221549045868670625406606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55024373334910902729/25000000000000000000)
  centralHi := (220097493339643610917/100000000000000000000)
  directionLo := (112766408898122435123/50000000000000000000)
  directionHi := (225532817796244870247/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree022.table
  base := (-6304050104797015780148867703135211847901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-2130808629630261658571832587380000000000000)
      constant := (5650575936506232517028907940273923775956611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree022.table
  base := (-6345874383476719232877290506343416050191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-58651200012322741613179921768980000000000000)
      constant := (160592223956357596822328954246842324560359627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112766408898122435123/50000000000000000000)
  centralHi := (225532817796244870247/100000000000000000000)
  directionLo := (57710049618672304319/25000000000000000000)
  directionHi := (230840198474689217277/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree023.table
  base := (-3330998612516099324056009729588798854391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-2249529373359651625574606729320000000000000)
      constant := (6448963513491482109041235765627674262162002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree023.table
  base := (-3349193253415947604379931249276035202169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-61907540411757437850970298233620000000000000)
      constant := (183056471815794712557372192966038194634950586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57710049618672304319/25000000000000000000)
  centralHi := (230840198474689217277/100000000000000000000)
  directionLo := (11801413322199340843/5000000000000000000)
  directionHi := (236028266443986816861/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree024.table
  base := (-3493986143840945515070247120278809315163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-2368250117089041592577380871260000000000000)
      constant := (7305476027242804908489827530398848215835786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree024.table
  base := (-7019592730004700228039240638680721854991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-21721293603730711362920224899420000000000000)
      constant := (69042376310588486919035898803111442455168409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11801413322199340843/5000000000000000000)
  centralHi := (236028266443986816861/100000000000000000000)
  directionLo := (30138090488116465833/12500000000000000000)
  directionHi := (48220944780986345333/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree025.table
  base := (-910606879397541343048913254084954015069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-2486970860818431559580155013200000000000000)
      constant := (8219281232196706185927306192805586317160472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree025.table
  base := (-1462459208467784933011174257743406555107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-68420221210626830326551051162900000000000000)
      constant := (232782323578420245130556961614140993252500395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30138090488116465833/12500000000000000000)
  centralHi := (48220944780986345333/20000000000000000000)
  directionLo := (24607647839237516117/10000000000000000000)
  directionHi := (246076478392375161171/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree026.table
  base := (-7555027694486446608908901954021299992209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-2605691604547821526582929155140000000000000)
      constant := (9189690664762055512938826535607844302251599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree026.table
  base := (-3789405520971567718533499767729526653829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-71676561610061526564341427627540000000000000)
      constant := (260003994946717918022361705168173007040344626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24607647839237516117/10000000000000000000)
  centralHi := (246076478392375161171/100000000000000000000)
  directionLo := (7842179782243213879/3125000000000000000)
  directionHi := (250949753031782844129/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree027.table
  base := (-7800466390169729968450541653713984732673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-2724412348277211493585703297080000000000000)
      constant := (10216133224938269890889540520206658412257503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree027.table
  base := (-3910526847850680448171096126617612054117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-24977634003165407600710601364060000000000000)
      constant := (96259064249020802066587498917015182094483366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7842179782243213879/3125000000000000000)
  centralHi := (250949753031782844129/100000000000000000000)
  directionLo := (255730177873931268947/100000000000000000000)
  directionHi := (63932544468482817237/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree028.table
  base := (-250712926211271762726020613295056020099/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-2843133092006601460588477439020000000000000)
      constant := (11298134225448030315940898577927321926124448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree028.table
  base := (-8040612747689688118090478159818053767651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-78189242408930919039922180556820000000000000)
      constant := (319089520009428002214903285277979726451019247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255730177873931268947/100000000000000000000)
  centralHi := (63932544468482817237/25000000000000000000)
  directionLo := (130211433065756796023/50000000000000000000)
  directionHi := (260422866131513592047/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree029.table
  base := (-8223436615899758904707117960853897567719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-2961853835735991427591251580960000000000000)
      constant := (12435298552531257437031312564283223602929209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree029.table
  base := (-8238807227849308702959954781866844767053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-81445582808365615277712557021460000000000000)
      constant := (350930684343183588007926965748453010282685441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130211433065756796023/50000000000000000000)
  centralHi := (260422866131513592047/100000000000000000000)
  directionLo := (132516239130221293341/50000000000000000000)
  directionHi := (265032478260442586683/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree030.table
  base := (-131304288632527802925779347449035575093/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-3080574579465381394594025722900000000000000)
      constant := (13627296991579336157438129583582638003079872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree030.table
  base := (-8416733195504496963551785759187837882697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-28233974402600103838500977828700000000000000)
      constant := (128097377732473950372535552760352433667105103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132516239130221293341/50000000000000000000)
  centralHi := (265032478260442586683/100000000000000000000)
  directionLo := (67390819043468235391/25000000000000000000)
  directionHi := (53912655234774588313/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree031.table
  base := (-1712775411170960294076881709507560674037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-3199295323194771361596799864840000000000000)
      constant := (14873855036708681872275067356531574826016535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree031.table
  base := (-1715060398522899181323128217101436766731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-87958263607235007753293309950740000000000000)
      constant := (419166755370834818362274687914747444545990035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67390819043468235391/25000000000000000000)
  centralHi := (53912655234774588313/20000000000000000000)
  directionLo := (17126198086547229331/6250000000000000000)
  directionHi := (274019169384755669297/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree032.table
  base := (-1741087355749961438876953496003986081271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-3318016066924161328599574006780000000000000)
      constant := (16174743680640040771902922951554240112563405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree032.table
  base := (-8715271704699269287737173972318769709023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-91214604006669703991083686415380000000000000)
      constant := (455548635522110212557096202640236639960493531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17126198086547229331/6250000000000000000)
  centralHi := (274019169384755669297/100000000000000000000)
  directionLo := (139201877249402730413/50000000000000000000)
  directionHi := (278403754498805460827/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree033.table
  base := (-8828814958172417796714199179713286867237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-3436736810653551295602348148720000000000000)
      constant := (17529771802758788318694818810592860095368507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree033.table
  base := (-4418636564159651670894354330828258891473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-31490314802034800076291354293340000000000000)
      constant := (164477617181895519870454152132311397246557454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139201877249402730413/50000000000000000000)
  centralHi := (278403754498805460827/100000000000000000000)
  directionLo := (282720349192892135993/100000000000000000000)
  directionHi := (141360174596446067997/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree034.table
  base := (-8934563649714819862052719454889239917357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (430)
      previous := (301)
      next := (0)
      square := (8480053123527854785912438710000000000000)
      linear := (-209144562022525956623830722980000000000000)
      constant := (1114045874058751917039895903826882921404931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree034.table
  base := (-4470915629672723661698959191221438541109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (11481)
      previous := (8256)
      next := (0)
      square := (228961434335252079219635845170000000000000)
      linear := (-5748663812090535086274378784980000000000000)
      constant := (31342076876399036634777277351738719419261938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282720349192892135993/100000000000000000000)
  centralHi := (141360174596446067997/50000000000000000000)
  directionLo := (286972021591775716847/100000000000000000000)
  directionHi := (17935751349485982303/6250000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree035.table
  base := (-2255785946769783133268682965388810372109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-3674178298112331229607896432600000000000000)
      constant := (20401634639520111152620254987260535209841996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree035.table
  base := (-282168222098086856422093471640520818157/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-100983625204973792704454815809300000000000000)
      constant := (573692591597356909113182085753248513789469728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286972021591775716847/100000000000000000000)
  centralHi := (17935751349485982303/6250000000000000000)
  directionLo := (291161615782696039459/100000000000000000000)
  directionHi := (14558080789134801973/5000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree036.table
  base := (-2273735068884631355762249531771642345597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-3792899041841721196610670574540000000000000)
      constant := (21918224906698827989286220537991981448489868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree036.table
  base := (-14560467971155607399595664709229848859/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-34746655201469496314081730757980000000000000)
      constant := (205353955609948850142144346048578226948588125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291161615782696039459/100000000000000000000)
  centralHi := (14558080789134801973/5000000000000000000)
  directionLo := (73822943517712548351/25000000000000000000)
  directionHi := (59058354814170038681/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree037.table
  base := (-366010982592910633306779318096164892117/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-3911619785571111163613444716480000000000000)
      constant := (23488457761563030349775571218685208654454675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree037.table
  base := (-457743114060277317012976997891395690397/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-107496306003843185180035568738580000000000000)
      constant := (659920769088155015509591506506508788556644180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73822943517712548351/25000000000000000000)
  centralHi := (59058354814170038681/20000000000000000000)
  directionLo := (37420619558821977973/12500000000000000000)
  directionHi := (59872991294115164757/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree038.table
  base := (-2297353782665425255118220573036645850697/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-4030340529300501130616218858420000000000000)
      constant := (25112255614626792376371201898449637396594268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree038.table
  base := (-4596672351944179792170810257494188162613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-110752646403277881417825945203220000000000000)
      constant := (705267330463097455995637126338185699534261522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37420619558821977973/12500000000000000000)
  centralHi := (59872991294115164757/20000000000000000000)
  directionLo := (60676691568130008243/20000000000000000000)
  directionHi := (2370183264380078447/781250000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree039.table
  base := (-2303146554444962191075537224895467173129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-4149061273029891097618993000360000000000000)
      constant := (26789553659164728431276499231590839947862876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree039.table
  base := (-9215949746945833148586868165928116816199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-38002995600904192551872107222620000000000000)
      constant := (250699970782889004631255698811140968161066401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60676691568130008243/20000000000000000000)
  centralHi := (2370183264380078447/781250000000000000)
  directionLo := (76837355750665478373/25000000000000000000)
  directionHi := (307349423002661913493/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree040.table
  base := (-2304993783907222905080137915107455509527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-4267782016759281064621767142300000000000000)
      constant := (28520297762745302255760278510135781430986788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree040.table
  base := (-4611426137150573742743767167854916288851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-117265327202147273893406698132500000000000000)
      constant := (800417150281671112133184378922456176396191294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76837355750665478373/25000000000000000000)
  centralHi := (307349423002661913493/100000000000000000000)
  directionLo := (311264860125245951823/100000000000000000000)
  directionHi := (19454053757827871989/6250000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree041.table
  base := (-9211738348156271078225281187206912911063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-4386502760488671031624541284240000000000000)
      constant := (30304442707287703259300051647067202168702793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree041.table
  base := (-9214197899955624462823647504470555226407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-120521667601581970131197074597140000000000000)
      constant := (850217908036057436179601411574776257568346179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311264860125245951823/100000000000000000000)
  centralHi := (19454053757827871989/6250000000000000000)
  directionLo := (157565826305633807093/50000000000000000000)
  directionHi := (315131652611267614187/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree042.table
  base := (-4594003278987000141262978208123706346833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-4505223504218060998627315426180000000000000)
      constant := (32141950719737059643132538769784497731530526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree042.table
  base := (-9190107884791342671559109960625539959377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-41259336000338888789662483687260000000000000)
      constant := (300500413137721042262575621611292970565660423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157565826305633807093/50000000000000000000)
  centralHi := (315131652611267614187/100000000000000000000)
  directionLo := (159475784843834812919/50000000000000000000)
  directionHi := (318951569687669625839/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree043.table
  base := (-9148888951585762955720807580085154541937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-4623944247947450965630089568120000000000000)
      constant := (34032790245193806811455751341085390337380207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree043.table
  base := (-9150683212893631330200199798066845349441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-127034348400451362606777827526420000000000000)
      constant := (954266356434170360065556250733124405738311877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159475784843834812919/50000000000000000000)
  centralHi := (318951569687669625839/100000000000000000000)
  directionLo := (322726275866945945343/100000000000000000000)
  directionHi := (1260649515105257599/390625000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree044.table
  base := (-1136809593057933060629123539846106997651/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-4742664991676840932632863710060000000000000)
      constant := (35976934922386564107362197958995800621430888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree044.table
  base := (-1819201597026347340784841318935907485703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-130290688799886058844568203991060000000000000)
      constant := (1008512602859996407405911178696275569445297455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322726275866945945343/100000000000000000000)
  centralHi := (1260649515105257599/390625000000000000)
  directionLo := (326457339423802539923/100000000000000000000)
  directionHi := (81614334855950634981/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree045.table
  base := (-2256211535414374980348111464164511450339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-4861385735406230899635637852000000000000000)
      constant := (37974362728055767361133123875675824763408116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree045.table
  base := (-564134515281464153402853163244681695701/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-44515676399773585027452860151900000000000000)
      constant := (354746477381709895914811082374409326551707184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326457339423802539923/100000000000000000000)
  centralHi := (81614334855950634981/25000000000000000000)
  directionLo := (2641169920075723331/800000000000000000)
  directionHi := (41268280001183177047/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree046.table
  base := (-2235015202606156400103609646152447382353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-4980106479135620866638411993940000000000000)
      constant := (40025055262364213991775719416167770825999932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree046.table
  base := (-4470587164240534979812034566203051317563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-136803369598755451320148956920340000000000000)
      constant := (1121446389082273302825684486597595181138111822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2641169920075723331/800000000000000000)
  centralHi := (41268280001183177047/12500000000000000000)
  directionLo := (16689718775424832367/5000000000000000000)
  directionHi := (333794375508496647341/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree047.table
  base := (-2210043486344732449817046282432744201047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-5098827222865010833641186135880000000000000)
      constant := (42128997152068432487188080397237747703589668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree047.table
  base := (-4420561413798761421929506510876860250669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-140059709998190147557939333384980000000000000)
      constant := (1180133094519499380212475201715095718928059586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16689718775424832367/5000000000000000000)
  centralHi := (333794375508496647341/100000000000000000000)
  directionLo := (337403068228234980909/100000000000000000000)
  directionHi := (33740306822823498091/10000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree048.table
  base := (-4362614996679996285853896837881242848161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-5217547966594400800643960277820000000000000)
      constant := (44286175552031784211835269553784641633762942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree048.table
  base := (-872603821621427805428347061183790658273/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-47772016799208281265243236616540000000000000)
      constant := (413433077545121730146108894840689604978319270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337403068228234980909/100000000000000000000)
  centralHi := (33740306822823498091/10000000000000000000)
  directionLo := (340973570498575025263/100000000000000000000)
  directionHi := (21310848156160939079/6250000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree049.table
  base := (-8595266094114251189757345525997005053741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-5336268710323790767646734419760000000000000)
      constant := (46496579728867548794102327389156865539468851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree049.table
  base := (-4297977105179282604434883001238425703349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-146572390797059540033520086314260000000000000)
      constant := (1301944540343710260794200890067633128473535506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340973570498575025263/100000000000000000000)
  centralHi := (21310848156160939079/6250000000000000000)
  directionLo := (172253534874662612819/50000000000000000000)
  directionHi := (344507069749325225639/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree050.table
  base := (-66018072528342095293944306020921745217/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-5454989454053180734649508561700000000000000)
      constant := (48760200713175748378713133091674062800932736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree050.table
  base := (-8450898898319181279384126455424200412271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-149828731196494236271310462778900000000000000)
      constant := (1365068798471617108509405947028324964183049387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172253534874662612819/50000000000000000000)
  centralHi := (344507069749325225639/100000000000000000000)
  directionLo := (348004693123506826033/100000000000000000000)
  directionHi := (174002346561753413017/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree051.table
  base := (-2072599374805774571580482055836912306493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (430)
      previous := (301)
      next := (0)
      square := (8480053123527854785912438710000000000000)
      linear := (-327865305751915923626604864920000000000000)
      constant := (3004531235827657764703843912413089963158476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree051.table
  base := (-8290895682038055005689631716595935670403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3827)
      previous := (2752)
      next := (0)
      square := (76320478111750693073211948390000000000000)
      linear := (-3001668070508410441354918416540000000000000)
      constant := (28032780870857507129937063610720821842428341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348004693123506826033/100000000000000000000)
  centralHi := (174002346561753413017/50000000000000000000)
  directionLo := (87866877919350916511/25000000000000000000)
  directionHi := (70293502335480733209/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree052.table
  base := (-8115540419083540414111129079217110171767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-5692430941511960668655056845580000000000000)
      constant := (53447064351555858918921072664986255160359337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree052.table
  base := (-2028991015241335002943678672854395115497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-156341411995363628746891215708180000000000000)
      constant := (1495753466015847977418372039461908619655107636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87866877919350916511/25000000000000000000)
  centralHi := (70293502335480733209/20000000000000000000)
  directionLo := (354896544211726025559/100000000000000000000)
  directionHi := (8872413605293150639/2500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree053.table
  base := (-3962880081742542512008173345668003460261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-5811151685241350635657830987520000000000000)
      constant := (55870295503873023677546412270133893999969142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree053.table
  base := (-3963060142372077214779013713861077776879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-159597752394798324984681592172820000000000000)
      constant := (1563313596481997199100790091044524020214026326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354896544211726025559/100000000000000000000)
  centralHi := (8872413605293150639/2500000000000000000)
  directionLo := (358292760772730836261/100000000000000000000)
  directionHi := (179146380386365418131/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree054.table
  base := (-1930267970129802731376698733308386418357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-5929872428970740602660605129460000000000000)
      constant := (58346720088223238899904762517015505300379308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree054.table
  base := (-7721377896677573290281714445614260557663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-54284697598077673740823989545820000000000000)
      constant := (544117370044595544735087315068077308289518537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358292760772730836261/100000000000000000000)
  centralHi := (179146380386365418131/50000000000000000000)
  directionLo := (90414271464349397499/25000000000000000000)
  directionHi := (361657085857397589997/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree055.table
  base := (-7501488235336461305499759601076954323743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-6048593172700130569663379271400000000000000)
      constant := (60876334444377997604977027810538760200438273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree055.table
  base := (-7501748186256090097196037739127566757663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-166110433193667717460262345102100000000000000)
      constant := (1702868918879321961925925807601587596589955611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90414271464349397499/25000000000000000000)
  centralHi := (361657085857397589997/100000000000000000000)
  directionLo := (364990401352672252827/100000000000000000000)
  directionHi := (91247600338168063207/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree056.table
  base := (-227094369337648551666599090268309611531/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-6167313916429520536666153413340000000000000)
      constant := (63459135511576471638345124324718672712561312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree056.table
  base := (-7267240565964570516876831540441771918617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-169366773593102413698052721566740000000000000)
      constant := (1774863949272983775466490443722892853719031549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364990401352672252827/100000000000000000000)
  centralHi := (91247600338168063207/25000000000000000000)
  directionLo := (23018346827203717463/6250000000000000000)
  directionHi := (368293549235259479409/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree057.table
  base := (-1403535097771579143390827889727322107687/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-6286034660158910503668927555280000000000000)
      constant := (66095120729875790560850603080874019554392285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree057.table
  base := (-7017862885040639185719135060744681721787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-57541037997512369978614366010460000000000000)
      constant := (616112380022390296596388454201083082841632013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23018346827203717463/6250000000000000000)
  centralHi := (368293549235259479409/100000000000000000000)
  directionLo := (92891833513845628263/25000000000000000000)
  directionHi := (371567334055382513053/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree058.table
  base := (-52761426997051907612958782555824968913/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-6404755403888300470671701697220000000000000)
      constant := (68784287957749321692525437060974922749970304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree058.table
  base := (-3376810845367847472624062803151928667327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-175879454391971806173633474496020000000000000)
      constant := (1923288440173680639733529605721851001217694838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92891833513845628263/25000000000000000000)
  centralHi := (371567334055382513053/100000000000000000000)
  directionLo := (374812525225270379619/100000000000000000000)
  directionHi := (18740626261263518981/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree059.table
  base := (-32371937597929508779862682501560704741/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-6523476147617690437674475839160000000000000)
      constant := (71526635403256350144362746554179791265970200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree059.table
  base := (-6474522445863952839178802225343426976619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-179135794791406502411423850960660000000000000)
      constant := (1999717806966173705313475035505405239301441943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374812525225270379619/100000000000000000000)
  centralHi := (18740626261263518981/5000000000000000000)
  directionLo := (378029859130814781489/100000000000000000000)
  directionHi := (37802985913081478149/10000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree060.table
  base := (-618045527053787918311034207688921984823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-6642196891347080404677249981100000000000000)
      constant := (74322161566547505017815864293779015463861530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree060.table
  base := (-6180569709954640828510264461633131191957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-60797378396947066216404742475100000000000000)
      constant := (692541734955547840249775226071292225769719843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378029859130814781489/100000000000000000000)
  centralHi := (37802985913081478149/10000000000000000000)
  directionLo := (381220041082815307703/100000000000000000000)
  directionHi := (47652505135351913463/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree061.table
  base := (-5871670253752649712573414634289297405437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-6760917635076470371680024123040000000000000)
      constant := (77170865191838579141698122169660393049828707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree061.table
  base := (-5871767290098268031435362536681388188697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-185648475590275894887004603889940000000000000)
      constant := (2157010604168362843391822723568835127963597309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (381220041082815307703/100000000000000000000)
  centralHi := (47652505135351913463/12500000000000000000)
  directionLo := (192191873561229894543/50000000000000000000)
  directionHi := (384383747122459789087/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree062.table
  base := (-693504513600384472249051724357198018127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-6879638378805860338682798264980000000000000)
      constant := (80072745227293015272690259550966158182090376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree062.table
  base := (-221924734662341842018230768971650094029/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-188904815989710591124794980354580000000000000)
      constant := (2237873980055733931606645618916295357907292825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192191873561229894543/50000000000000000000)
  centralHi := (384383747122459789087/100000000000000000000)
  directionLo := (387521625694131858949/100000000000000000000)
  directionHi := (7750432513882637179/2000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree063.table
  base := (-520955588551799734208103936752103509181/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-6998359122535250305685572406920000000000000)
      constant := (83027800791510278661568017192916420858466910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree063.table
  base := (-5209625597372797327020076473855975185199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-64053718796381762454195118939740000000000000)
      constant := (773405103929363852794390333758380608543297401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387521625694131858949/100000000000000000000)
  centralHi := (7750432513882637179/2000000000000000000)
  directionLo := (39063429919727038807/10000000000000000000)
  directionHi := (390634299197270388071/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree064.table
  base := (-1214058035211737394625253581595847518247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-7117079866264640272688346548860000000000000)
      constant := (86036031145531953643143157155995200268906468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree064.table
  base := (-242814560272848792201223051840280940011/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-195417496788579983600375733283860000000000000)
      constant := (2404034582020022534792860003453965756501883340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39063429919727038807/10000000000000000000)
  centralHi := (390634299197270388071/100000000000000000000)
  directionLo := (24607647839237516117/6250000000000000000)
  directionHi := (393722365427800257873/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree065.table
  base := (-4488067019777393684363235835422770424637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-7235800609994030239691120690800000000000000)
      constant := (89097435669456663931450630159812819347279907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree065.table
  base := (-4488117051142985574967362382974239147113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-198673837188014679838166109748500000000000000)
      constant := (2489331776235357014130504302269652011935077261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24607647839237516117/6250000000000000000)
  centralHi := (393722365427800257873/100000000000000000000)
  directionLo := (396786398918589454869/100000000000000000000)
  directionHi := (39678639891858945487/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree066.table
  base := (-4105062322931345050053146962310425315637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-7354521353723420206693894832740000000000000)
      constant := (92212013842904647078669043157812287083780907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree066.table
  base := (-513138086573252348388543058665233132009/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-67310059195816458691985495404380000000000000)
      constant := (858702294091936677044892506722013828989156728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396786398918589454869/100000000000000000000)
  centralHi := (39678639891858945487/10000000000000000000)
  directionLo := (99956738046861343801/25000000000000000000)
  directionHi := (79965390437489075041/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree067.table
  base := (-463402445379441772105376635039762441781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-7473242097452810173696668974680000000000000)
      constant := (95379765228697877969930711457118069234602328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree067.table
  base := (-3707255436071669838363552439433624624699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-205186517986884072313746862677780000000000000)
      constant := (2664359889948435093030559976587739427053473703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99956738046861343801/25000000000000000000)
  centralHi := (79965390437489075041/20000000000000000000)
  directionLo := (201422278450163906693/50000000000000000000)
  directionHi := (402844556900327813387/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree068.table
  base := (-1647270006048888672197053256132193422829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (430)
      previous := (301)
      next := (0)
      square := (8480053123527854785912438710000000000000)
      linear := (-446586049481305890629379006860000000000000)
      constant := (5800040556425064570612560432731505423623814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree068.table
  base := (-8236425944782221285091143366640179191/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (11481)
      previous := (8256)
      next := (0)
      square := (228961434335252079219635845170000000000000)
      linear := (-12261344610959927561855131714260000000000000)
      constant := (162005340629335426626084040406204863100532400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201422278450163906693/50000000000000000000)
  centralHi := (402844556900327813387/100000000000000000000)
  directionLo := (101459931239178471707/25000000000000000000)
  directionHi := (405839724956713886829/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree069.table
  base := (-2867024740820322060531100418243199342207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-7710683584911590107702217258560000000000000)
      constant := (101874786225056356740356160312497715390102177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree069.table
  base := (-1433525219671997286336169586612337168631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-70566399595251154929775871869020000000000000)
      constant := (948433192446073370965784943805962622048781538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101459931239178471707/25000000000000000000)
  centralHi := (405839724956713886829/100000000000000000000)
  directionLo := (408812949503389507851/100000000000000000000)
  directionHi := (102203237375847376963/25000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree070.table
  base := (-2424674651528757387198522715086451847391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-7829404328640980074704991400500000000000000)
      constant := (105202055265416559850856641757340015416104001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree070.table
  base := (-2424696395583468356196912202831068035663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-214955539185188161027117992071700000000000000)
      constant := (2937986243817958871684292061569309176117721611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408812949503389507851/100000000000000000000)
  centralHi := (102203237375847376963/25000000000000000000)
  directionLo := (51470588235294117647/12500000000000000000)
  directionHi := (411764705882352941177/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree071.table
  base := (-983745252842223931035040165087886448951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-7948125072370370041707765542440000000000000)
      constant := (108582496360244372680527270388949201632506322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree071.table
  base := (-983754450020569726171832915784041290407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-218211879584622857264908368536340000000000000)
      constant := (3032150785039361628731155959602034251621908358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51470588235294117647/12500000000000000000)
  centralHi := (411764705882352941177/100000000000000000000)
  directionLo := (103673863129497453999/25000000000000000000)
  directionHi := (414695452517989815997/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree072.table
  base := (-186934118359064772099721154267155701723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-8066845816099760008710539684380000000000000)
      constant := (112016109323543694193480619371814336017616424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree072.table
  base := (-747744252241060243433436511312546349789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-73822739994685851167566248333660000000000000)
      constant := (1042597732232335070073061977861432133888397622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103673863129497453999/25000000000000000000)
  centralHi := (414695452517989815997/100000000000000000000)
  directionLo := (10440140793705204781/2500000000000000000)
  directionHi := (417605631748208191241/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree073.table
  base := (-504311260005233830038557789909900561917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-8185566559829149975713313826320000000000000)
      constant := (115502893997833367083723681647762077475211974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree073.table
  base := (-252158918955970994003099168630096550877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-224724560383492249740489121465620000000000000)
      constant := (3224913475147532578104115515318957426454027076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10440140793705204781/2500000000000000000)
  centralHi := (417605631748208191241/100000000000000000000)
  directionLo := (42049567060380038161/10000000000000000000)
  directionHi := (420495670603800381611/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree074.table
  base := (-253469843699877121391842403893831632103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-8304287303558539942716087968260000000000000)
      constant := (119042850249508270009233418804469365316644466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree074.table
  base := (-253475405064841841770208109240477715679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-227980900782926945978279497930260000000000000)
      constant := (3323511617300462163267324024704153104769113526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42049567060380038161/10000000000000000000)
  centralHi := (420495670603800381611/100000000000000000000)
  directionLo := (423365981539919566989/100000000000000000000)
  directionHi := (42336598153991956699/10000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree075.table
  base := (9575157859831201802182758988657957987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-8423008047287929909718862110200000000000000)
      constant := (122635977964962563407631812488597722149858243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree075.table
  base := (9565755732729709069267920616262734693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-77079080394120547405356624798300000000000000)
      constant := (1141195873509071635713741526341522899372936493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423365981539919566989/100000000000000000000)
  centralHi := (42336598153991956699/10000000000000000000)
  directionLo := (426216963123218781579/100000000000000000000)
  directionHi := (21310848156160939079/5000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree076.table
  base := (108184336131761723860734506498445668219/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-8541728791017319876721636252140000000000000)
      constant := (126282277047349607543203963284210253990576455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree076.table
  base := (270456867188313088149947952325408341799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-234493581581796338453860250859540000000000000)
      constant := (3525141482585312155336709901263350322582115194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426216963123218781579/100000000000000000000)
  centralHi := (21310848156160939079/5000000000000000000)
  directionLo := (429049000677893389191/100000000000000000000)
  directionHi := (53631125084736673649/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree077.table
  base := (1087099594507001480444424445468588910333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-8660449534746709843724410394080000000000000)
      constant := (129981747413873741398989003131870422195086237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree077.table
  base := (217418575960183560645760089631128671291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-237749921981231034691650627324180000000000000)
      constant := (3628173201555207418853638418591998485110418365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429049000677893389191/100000000000000000000)
  centralHi := (53631125084736673649/12500000000000000000)
  directionLo := (431862466893591813467/100000000000000000000)
  directionHi := (107965616723397953367/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree078.table
  base := (412027163424987171627758677517521220913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-8779170278476099810727184536020000000000000)
      constant := (133734388993526375717458758336890254531375428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree078.table
  base := (824051490321580865296880962700525304797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-80335420793555243643147001262940000000000000)
      constant := (1244227591929213185353729010423648132635553994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431862466893591813467/100000000000000000000)
  centralHi := (107965616723397953367/25000000000000000000)
  directionLo := (54332215299738723517/12500000000000000000)
  directionHi := (434657722397909788137/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree079.table
  base := (1111974323384851786136449784071155421351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-8897891022205489777729958677960000000000000)
      constant := (137540201725193273912361584413163127833540878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree079.table
  base := (1111971927277761684771747562416873584043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-244262602780100427167231380253460000000000000)
      constant := (3838670203859748413662549160794437729152575058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54332215299738723517/12500000000000000000)
  centralHi := (434657722397909788137/100000000000000000000)
  directionLo := (218717558147978903573/50000000000000000000)
  directionHi := (437435116295957807147/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree080.table
  base := (1407309695504332589604831246448873166071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-9016611765934879744732732819900000000000000)
      constant := (141399185556071939306685098324447448689989038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree080.table
  base := (56292306870319960507365613896365936739/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-247518943179535123405021756718100000000000000)
      constant := (3946135484538488289024904867061667170218720850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218717558147978903573/50000000000000000000)
  centralHi := (437435116295957807147/100000000000000000000)
  directionLo := (440194986679287221833/100000000000000000000)
  directionHi := (220097493339643610917/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree081.table
  base := (342012072788989816458472446821684868911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-9135332509664269711735506961840000000000000)
      constant := (145311340440348087586378422955084669271152790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree081.table
  base := (855029327479648890231354387347905253547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-83591761192989939880937377727580000000000000)
      constant := (1351692872250039880369376551166287606257902988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440194986679287221833/100000000000000000000)
  centralHi := (220097493339643610917/50000000000000000000)
  directionLo := (221468830553137645053/50000000000000000000)
  directionHi := (442937661106275290107/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree082.table
  base := (4040452519236474000903126434643801954829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-9254053253393659678738281103780000000000000)
      constant := (149276666338088586406995515136892058764945581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree082.table
  base := (16161798533249371699361625918957552867/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-254031623978404515880602509647380000000000000)
      constant := (4165499599554763527192348302779646446255300250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221468830553137645053/50000000000000000000)
  centralHi := (442937661106275290107/100000000000000000000)
  directionLo := (445663457055901433303/100000000000000000000)
  directionHi := (55707932131987679163/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree083.table
  base := (2337807322008326164379430389099927216413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-9372773997123049645741055245720000000000000)
      constant := (153295163214315262804668038669429757931086714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree083.table
  base := (584451525960091626118926045383819982089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-257287964377839212118392886112020000000000000)
      constant := (4277398432125173142312573984228879578561923736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445663457055901433303/100000000000000000000)
  centralHi := (55707932131987679163/12500000000000000000)
  directionLo := (224186341178347116659/50000000000000000000)
  directionHi := (448372682356694233319/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree084.table
  base := (5325606995662006621584135065012011734353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-9491494740852439612743829387660000000000000)
      constant := (157366831038229841513217901539308471391228017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree084.table
  base := (1331401234792844472317361159615013633163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-86848101592424636118727754192220000000000000)
      constant := (1463591704576339434499306899378554601839427852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224186341178347116659/50000000000000000000)
  centralHi := (448372682356694233319/100000000000000000000)
  directionLo := (451065635592489740493/100000000000000000000)
  directionHi := (225532817796244870247/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree085.table
  base := (5990429479822541857674136685160708642171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (430)
      previous := (301)
      next := (0)
      square := (8480053123527854785912438710000000000000)
      linear := (-565306793210695857632153148800000000000000)
      constant := (9499509987209716115963083111897732046916907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree085.table
  base := (1198085548840143990846027213643069290699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (11481)
      previous := (8256)
      next := (0)
      square := (228961434335252079219635845170000000000000)
      linear := (-15517685010394623799645508178900000000000000)
      constant := (265037037865535088865020681959310844022154205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451065635592489740493/100000000000000000000)
  centralHi := (225532817796244870247/50000000000000000000)
  directionLo := (56717825810814384151/12500000000000000000)
  directionHi := (453742606486515073209/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree086.table
  base := (6670082012487004232624421756918026422209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-9728936228311219546749377671540000000000000)
      constant := (165669679423042007829658688476469309636018401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree086.table
  base := (833760068483902945464181788203174039793/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-267056985576143300831764015505940000000000000)
      constant := (4621962021495982293335010088557354936260038232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56717825810814384151/12500000000000000000)
  centralHi := (453742606486515073209/100000000000000000000)
  directionLo := (45640387626519583907/10000000000000000000)
  directionHi := (456403876265195839071/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree087.table
  base := (7364564518408403938740336767738270579589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-9847656972040609513752151813480000000000000)
      constant := (169900859937913963033652973396806360197501221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree087.table
  base := (7364563282648935547539639472788631752053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-90104441991859332356518130656860000000000000)
      constant := (1579924082182569404933327839185203231187089853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45640387626519583907/10000000000000000000)
  centralHi := (456403876265195839071/100000000000000000000)
  directionLo := (45904971800298049737/10000000000000000000)
  directionHi := (459049718002980497371/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree088.table
  base := (8073876929784645780153224953926950192327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-9966377715769999480754925955420000000000000)
      constant := (174185211307586234071749225858564888605582503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree088.table
  base := (1009234485907252138502182569139072280239/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-273569666375012693307344768435220000000000000)
      constant := (4859060318391138904961887204680577448021639336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45904971800298049737/10000000000000000000)
  centralHi := (459049718002980497371/100000000000000000000)
  directionLo := (461680396949378434553/100000000000000000000)
  directionHi := (230840198474689217277/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree089.table
  base := (1759603837030481939200825458971928147437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-10085098459499389447757700097360000000000000)
      constant := (178522733514295921446359206704784436173046465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree089.table
  base := (8798018305756105676684092137943343756573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-276826006774447389545135144899860000000000000)
      constant := (4979826236589756108699005723268531911332539119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461680396949378434553/100000000000000000000)
  centralHi := (230840198474689217277/50000000000000000000)
  directionLo := (464296170839320365939/100000000000000000000)
  directionHi := (23214808541966018297/5000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree090.table
  base := (9536991228459312086766229404945593125059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-10203819203228779414760474239300000000000000)
      constant := (182913426541843886297219666578029276413142051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree090.table
  base := (4768495243380203532933946935853353117599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-93360782391294028594308507121500000000000000)
      constant := (1700690000247539960988312421208309142917749998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464296170839320365939/100000000000000000000)
  centralHi := (23214808541966018297/5000000000000000000)
  directionLo := (93379458037573785547/20000000000000000000)
  directionHi := (58362161273483615967/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree091.table
  base := (643174563017820811929592196605076414887/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-10322539946958169381763248381240000000000000)
      constant := (187357290375369685055438015254271873342437488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree091.table
  base := (321587261962482783566331905742144773219/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-283338687573316782020715897829140000000000000)
      constant := (5225791610479310330171796777804350581293691424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93379458037573785547/20000000000000000000)
  centralHi := (58362161273483615967/12500000000000000000)
  directionLo := (234741999285116642763/50000000000000000000)
  directionHi := (469483998570233285527/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree092.table
  base := (1105942447718770057657503683410412310587/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-10441260690687559348766022523180000000000000)
      constant := (191854325001162530061638263533136091577596430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree092.table
  base := (2211884789953923351818662641674253554721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-286595027972751478258506274293780000000000000)
      constant := (5350991065455686942924388510853561002437439815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234741999285116642763/50000000000000000000)
  centralHi := (469483998570233285527/100000000000000000000)
  directionLo := (11801413322199340843/2500000000000000000)
  directionHi := (472056532887973633721/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree093.table
  base := (185045087361766238041444086047300171567/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-10559981434416949315768796665120000000000000)
      constant := (196404530406502382364756266948260863973303232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree093.table
  base := (11842885146479077768418738304568131162141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-96617122790728724832098883586140000000000000)
      constant := (1825889455116776617792412589198661709152728741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11801413322199340843/2500000000000000000)
  centralHi := (472056532887973633721/100000000000000000000)
  directionLo := (118653780905554758489/25000000000000000000)
  directionHi := (474615123622219033957/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree094.table
  base := (3160294077283185298466731758248936581311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-10678702178146339282771570807060000000000000)
      constant := (201007906579526252118904040583655770687995516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree094.table
  base := (12641175934264610723819129585435061577793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-293107708771620870734087027223060000000000000)
      constant := (5605823509861549945115627528573709785491518779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118653780905554758489/25000000000000000000)
  centralHi := (474615123622219033957/100000000000000000000)
  directionLo := (47715999507466463553/10000000000000000000)
  directionHi := (477159995074664635531/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree095.table
  base := (840893537040895184926617732696489696329/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-10797422921875729249774344949000000000000000)
      constant := (205664453509115591593913102899238568355825296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree095.table
  base := (6727148138334634178003706359644211972107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-296364049171055566971877403687700000000000000)
      constant := (5735456498704873658597310752776607572036701842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47715999507466463553/10000000000000000000)
  centralHi := (477159995074664635531/100000000000000000000)
  directionLo := (479691365597061484591/100000000000000000000)
  directionHi := (29980710349816342787/6250000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree096.table
  base := (14282246405492667969009431832614329275033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-10916143665605119216777119090940000000000000)
      constant := (210374171184801342103793214428745541160484537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree096.table
  base := (1428224613917082121079364703072578130501/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-99873463190163421069889260050780000000000000)
      constant := (1955522443870308012463747777704837757174331010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479691365597061484591/100000000000000000000)
  centralHi := (29980710349816342787/6250000000000000000)
  directionLo := (30138090488116465833/6250000000000000000)
  directionHi := (482209447809863453329/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree097.table
  base := (15125025713392611687957019985453618902731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-11034864409334509183779893232880000000000000)
      constant := (215137059596683761097507275824526095862889259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree097.table
  base := (15125025488952605000152366929769432877913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-302876729969924959447458156616980000000000000)
      constant := (5999156008323632650057962561588830884746355139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30138090488116465833/6250000000000000000)
  centralHi := (482209447809863453329/100000000000000000000)
  directionLo := (484714448810650938273/100000000000000000000)
  directionHi := (242357224405325469137/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree098.table
  base := (499457327619823697597674476938978981871/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-11153585153063899150782667374820000000000000)
      constant := (219953118735364627591010341324811677624343008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree098.table
  base := (1598263429470979143307532923784095220771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-306133070369359655685248533081620000000000000)
      constant := (6133222528598727921442731116677112950076761130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484714448810650938273/100000000000000000000)
  centralHi := (242357224405325469137/50000000000000000000)
  directionLo := (243603285186454778223/50000000000000000000)
  directionHi := (487206570372909556447/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree099.table
  base := (4213768171458695640630131649096428153017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-11272305896793289117785441516760000000000000)
      constant := (224822348591889818369135972955525470944887652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree099.table
  base := (8427536263242632785100789636667286810263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-103129803589598117307679636515420000000000000)
      constant := (2089588964067484827891238489666263225986988126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243603285186454778223/50000000000000000000)
  centralHi := (487206570372909556447/100000000000000000000)
  directionLo := (122421502283925952471/25000000000000000000)
  directionHi := (97937201827140761977/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree100.table
  base := (3548468057955761874494099046240320459417/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-11391026640522679084788215658700000000000000)
      constant := (229744749157700576747153149191817263063857565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree100.table
  base := (2217792519441282685879019335148886300189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-312645751168229048160829286010900000000000000)
      constant := (6405789098910485716242050215297334078402998136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122421502283925952471/25000000000000000000)
  centralHi := (97937201827140761977/20000000000000000000)
  directionLo := (24607647839237516117/5000000000000000000)
  directionHi := (492152956784750322341/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree101.table
  base := (9322218633638008507648773828861033991077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-11509747384252069051790989800640000000000000)
      constant := (234720320424592070842872944937651677646842506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree101.table
  base := (3728887430837142968940189093741514362817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-315902091567663744398619662475540000000000000)
      constant := (6544289148506997940111563099299685182865305255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24607647839237516117/5000000000000000000)
  centralHi := (492152956784750322341/100000000000000000000)
  directionLo := (494607600225362531299/100000000000000000000)
  directionHi := (4946076002253625313/1000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree102.table
  base := (4890340897759600976579761121896648740233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (430)
      previous := (301)
      next := (0)
      square := (8480053123527854785912438710000000000000)
      linear := (-684027536940085824634927290740000000000000)
      constant := (14102886022628121658724828082928972114335844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree102.table
  base := (19561363495780962949637860251552447663421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3827)
      previous := (2752)
      next := (0)
      square := (76320478111750693073211948390000000000000)
      linear := (-6258008469943106679145294881180000000000000)
      constant := (131064059623213332829104445057527524492503413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494607600225362531299/100000000000000000000)
  centralHi := (4946076002253625313/1000000000000000000)
  directionLo := (49705012174770842189/10000000000000000000)
  directionHi := (497050121747708421891/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree103.table
  base := (10246559617387962268786003316495874562711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-11747188871710848985796538084520000000000000)
      constant := (244830975030360745661699245651864615497246958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree103.table
  base := (640409973579593206057068063653130930281/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-322414772366533136874200415404820000000000000)
      constant := (6825722775540056130668186537292972180767444576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49705012174770842189/10000000000000000000)
  centralHi := (497050121747708421891/100000000000000000000)
  directionLo := (499480699184794815119/100000000000000000000)
  directionHi := (6243508739809935189/1250000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree104.table
  base := (10719852086553477500528682278234814313917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-11865909615440238952799312226460000000000000)
      constant := (249966058354304813923592718567539722673444026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree104.table
  base := (10719852052770911094755095905045144968927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-325671112765967833111990791869460000000000000)
      constant := (6968656352580904361023884835541494532385074762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499480699184794815119/100000000000000000000)
  centralHi := (6243508739809935189/1250000000000000000)
  directionLo := (7842179782243213879/1562500000000000000)
  directionHi := (501899506063565688257/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree105.table
  base := (22401118381481312647012825667992722792799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-11984630359169628919802086368400000000000000)
      constant := (255154312349415270198221193598299896887118911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree105.table
  base := (22401118324586273086065265326663792691709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-109642484388467509783260389444700000000000000)
      constant := (2371022590572584766750199185354652524791135109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7842179782243213879/1562500000000000000)
  centralHi := (501899506063565688257/100000000000000000000)
  directionLo := (252153355874738921873/50000000000000000000)
  directionHi := (504306711749477843747/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree106.table
  base := (11688680918056921073576243943999415076747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-12103351102899018886804860510340000000000000)
      constant := (260395737008818204595710045043151661914359766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree106.table
  base := (2337736178820814850451459147826240085489/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-332183793564837225587571544798740000000000000)
      constant := (7258957032767452474911968672993841513870706670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252153355874738921873/50000000000000000000)
  centralHi := (504306711749477843747/100000000000000000000)
  directionLo := (253351240792447401741/50000000000000000000)
  directionHi := (506702481584894803483/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree107.table
  base := (2436843451392690425660239257206272497279/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-12222071846628408853807634652280000000000000)
      constant := (265690332325844179374290698853856127517136310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree107.table
  base := (24368434473593808089627668846145858396723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-335440133964271921825361921263380000000000000)
      constant := (7406324135551984049316134583760716133069629569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253351240792447401741/50000000000000000000)
  centralHi := (506702481584894803483/100000000000000000000)
  directionLo := (254543488510809474911/50000000000000000000)
  directionHi := (509086977021618949823/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree108.table
  base := (25374336392500374370310340529588471781089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-12340792590357798820810408794220000000000000)
      constant := (271038098294013778523103069464331068344734721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree108.table
  base := (3171792044818223836091763195531206013687/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-112898824787902206021050765909340000000000000)
      constant := (2518389693299380744696269406877893334732799096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254543488510809474911/50000000000000000000)
  centralHi := (509086977021618949823/100000000000000000000)
  directionLo := (102292071149572507579/20000000000000000000)
  directionHi := (63932544468482817237/12500000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree109.table
  base := (13197533725013992155537541491027241493503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-12459513334087188787813182936160000000000000)
      constant := (276439034907024990538935995977583745583244734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree109.table
  base := (26395067421445605137526558819716436906669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-341952814763141314300942674192660000000000000)
      constant := (7705491865637237942674899387644007357182738207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102292071149572507579/20000000000000000000)
  centralHi := (63932544468482817237/12500000000000000000)
  directionLo := (4110582174479521207/800000000000000000)
  directionHi := (128455692952485037719/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree110.table
  base := (27430627665279029984870222055456053221019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-12578234077816578754815957078100000000000000)
      constant := (281893142158742141938615849408026799380874491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree110.table
  base := (13715313820610442412685594282903645331137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-345209155162576010538733050657300000000000000)
      constant := (7857292492604843498411632230906994289037724022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4110582174479521207/800000000000000000)
  centralHi := (128455692952485037719/25000000000000000000)
  directionLo := (258087187864474178247/50000000000000000000)
  directionHi := (103234875145789671299/20000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree111.table
  base := (28481017017564625707306478016712760499641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-12696954821545968721818731220040000000000000)
      constant := (287400420043186144759354127912799987784396249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree111.table
  base := (7120254249329060459440282979714945046091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-116155165187336902258841142373980000000000000)
      constant := (2670190320213521736467369899780474288259530764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258087187864474178247/50000000000000000000)
  centralHi := (103234875145789671299/20000000000000000000)
  directionLo := (103703062922536530711/20000000000000000000)
  directionHi := (129628828653170663389/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree112.table
  base := (14773117743353909124275043751108253991949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-12815675565275358688821505361980000000000000)
      constant := (292960868554525859517728873879820570807346522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree112.table
  base := (9454795350293524758783822610813512783/3200000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-351721835961445403014313803586580000000000000)
      constant := (8165327269587840474245145145000995750767965625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103703062922536530711/20000000000000000000)
  centralHi := (129628828653170663389/25000000000000000000)
  directionLo := (520845732263027184093/100000000000000000000)
  directionHi := (260422866131513592047/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree113.table
  base := (6125256610603396845505388448237721098993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-12934396309004748655824279503920000000000000)
      constant := (298574487687070407056609670018833506988044885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree113.table
  base := (30626283038677195499506592104435398786497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-354978176360880099252104180051220000000000000)
      constant := (8321561419293755786941259635359549416731036091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520845732263027184093/100000000000000000000)
  centralHi := (260422866131513592047/50000000000000000000)
  directionLo := (523165769279039050283/100000000000000000000)
  directionHi := (130791442319759762571/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree114.table
  base := (31721159697262026972194233670015618731049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-13053117052734138622827053645860000000000000)
      constant := (304241277435262289437776144654954513813273161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree114.table
  base := (31721159685195892749300735633220293531429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-119411505586771598496631518838620000000000000)
      constant := (2826424469869627532491718235684725983475246829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523165769279039050283/100000000000000000000)
  centralHi := (130791442319759762571/25000000000000000000)
  directionLo := (65684445394492042711/12500000000000000000)
  directionHi := (525475563155936341689/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree115.table
  base := (32830865400652966326737331705610020510317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-13171837796463528589829827787800000000000000)
      constant := (309961237793671202396197869694171295927481613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree115.table
  base := (32830865390500758821733834143544900432593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-361490857159749491727684932980500000000000000)
      constant := (8638463240387128475222419087566080858075523179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65684445394492042711/12500000000000000000)
  centralHi := (525475563155936341689/100000000000000000000)
  directionLo := (527775248380187081021/100000000000000000000)
  directionHi := (263887624190093540511/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree116.table
  base := (16977700072410289807252478008041004226829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-13290558540192918556832601929740000000000000)
      constant := (315734368756988440578322625120567700443107162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree116.table
  base := (2122212508517459453997798587647167749199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-364747197559184187965475309445140000000000000)
      constant := (8799130911485601431723533593746733599151996752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527775248380187081021/100000000000000000000)
  centralHi := (263887624190093540511/50000000000000000000)
  directionLo := (106012991304177034673/20000000000000000000)
  directionHi := (265032478260442586683/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree117.table
  base := (4386845488974850766716366362584886840309/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-13409279283922308523835376071680000000000000)
      constant := (321560670320021812441339986156626258374794408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree117.table
  base := (8773690976153362671184387508425168183661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-122667845986206294734421895303260000000000000)
      constant := (2987092140921495200356175845872535449782809044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106012991304177034673/20000000000000000000)
  centralHi := (265032478260442586683/50000000000000000000)
  directionLo := (266172408158794519169/50000000000000000000)
  directionHi := (532344816317589038339/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree118.table
  base := (36248956684008672906224917308928660377681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-13528000027651698490838150213620000000000000)
      constant := (327440142477690994794552944816760382849149809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree118.table
  base := (36248956677964389670731777251130736750331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-371259878358053580441056062374420000000000000)
      constant := (9124899774086926761431262034720013138862832793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266172408158794519169/50000000000000000000)
  centralHi := (532344816317589038339/100000000000000000000)
  directionLo := (534614953764788864833/100000000000000000000)
  directionHi := (267307476882394432417/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree119.table
  base := (37417978444243537366273521191734182237663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (430)
      previous := (301)
      next := (0)
      square := (8480053123527854785912438710000000000000)
      linear := (-802748280669475791637701432680000000000000)
      constant := (19610163836766074584498254718869481098040271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree119.table
  base := (1870898921957973954949614287081207989581/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (11481)
      previous := (8256)
      next := (0)
      square := (228961434335252079219635845170000000000000)
      linear := (-22030365809264016275226261108180000000000000)
      constant := (546470645018760377622665756923085489344353580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (534614953764788864833/100000000000000000000)
  centralHi := (267307476882394432417/50000000000000000000)
  directionLo := (268437746096579652953/50000000000000000000)
  directionHi := (536875492193159305907/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree120.table
  base := (1544073167026218979141318022933494433503/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-13765441515110478424843698497500000000000000)
      constant := (339358598557149581531877786487694497282059175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree120.table
  base := (19300914585689696779614998530901823684181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-125924186385640990972212271767900000000000000)
      constant := (3152193332109747793118069785813751286805109562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268437746096579652953/50000000000000000000)
  centralHi := (536875492193159305907/100000000000000000000)
  directionLo := (67390819043468235391/12500000000000000000)
  directionHi := (539126552347745883129/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree121.table
  base := (9950127215435665605263502443165196885581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-13884162258839868391846472639440000000000000)
      constant := (345397582469300909074231996065668967599731636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree121.table
  base := (39800508858146398933883384590138092029327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-381028899556357669154427191768340000000000000)
      constant := (9624636866989301881418603911738607532104838581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67390819043468235391/12500000000000000000)
  centralHi := (539126552347745883129/100000000000000000000)
  directionLo := (270684126231612677287/50000000000000000000)
  directionHi := (21654730098529014183/4000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree122.table
  base := (20507008743168821653835377046705483790689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-14002883002569258358849246781380000000000000)
      constant := (351489736956804855234431000937475769631018242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree122.table
  base := (41014017483313323029605220390536505478211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-384285239955792365392217568232980000000000000)
      constant := (9794171577173105541153813110999196352246480433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270684126231612677287/50000000000000000000)
  centralHi := (21654730098529014183/4000000000000000000)
  directionLo := (543600708336372781417/100000000000000000000)
  directionHi := (271800354168186390709/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree123.table
  base := (42242355033596354158775449504690253351119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-14121603746298648325852020923320000000000000)
      constant := (357635062015082485811368165968185483218473391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree123.table
  base := (42242355031053185091113443808384596807153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-129180526785075687210002648232540000000000000)
      constant := (3321728042252385475908790345311688336295404953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543600708336372781417/100000000000000000000)
  centralHi := (271800354168186390709/50000000000000000000)
  directionLo := (545824033395860970087/100000000000000000000)
  directionHi := (68228004174482621261/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree124.table
  base := (21742760743993919525392933447434678581673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-14240324490028038292854795065260000000000000)
      constant := (363833557639645354543128226944537244220206994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree124.table
  base := (1358922546432794141875624639430508365299/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-390797920754661757867798321162260000000000000)
      constant := (10137674515620378725307115604568200216781699104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545824033395860970087/100000000000000000000)
  centralHi := (68228004174482621261/12500000000000000000)
  directionLo := (17126198086547229331/3125000000000000000)
  directionHi := (548038338769511338593/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree125.table
  base := (44743516834284566575279742196860869558143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-14359045233757428259857569207200000000000000)
      constant := (370085223826092704852677149551142791302303327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree125.table
  base := (44743516832486583769673934534140723403073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-394054261154096454105588697626900000000000000)
      constant := (10311642743644046499099349689569900064714178619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17126198086547229331/3125000000000000000)
  centralHi := (548038338769511338593/100000000000000000000)
  directionLo := (550243733349109027291/100000000000000000000)
  directionHi := (137560933337277256823/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree126.table
  base := (23008170528776643915314977076458007867889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-14477765977486818226860343349140000000000000)
      constant := (376390060570108827807444695744512728547639842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree126.table
  base := (9203268211208328925469020387737967028939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-132436867184510383447793024697180000000000000)
      constant := (3495696270237238385849773231907652261211351695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550243733349109027291/100000000000000000000)
  centralHi := (137560933337277256823/25000000000000000000)
  directionLo := (69055040481611152389/12500000000000000000)
  directionHi := (552440323852889219113/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree127.table
  base := (23651997071573189748101470828518445428587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-14596486721216208193863117491080000000000000)
      constant := (382748067867460560267767766365013661457723286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree127.table
  base := (47303994141875553606481431345495861594459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-400566941952965846581169450556180000000000000)
      constant := (10664012716709156259781399904075944208021563577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69055040481611152389/12500000000000000000)
  centralHi := (552440323852889219113/100000000000000000000)
  directionLo := (554628214885796126759/100000000000000000000)
  directionHi := (13865705372144903169/2500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree128.table
  base := (48606476076693624389403592570273781771747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-14715207464945598160865891633020000000000000)
      constant := (389159245713994909467876374004489122932034883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree128.table
  base := (48606476075625316986954826752422941311451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (195177)
      previous := (140352)
      next := (0)
      square := (3892344383699285346733809367890000000000000)
      linear := (-403823282352400542818959827020820000000000000)
      constant := (10842414461524295365797430781524196211053252153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell021.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554628214885796126759/100000000000000000000)
  centralHi := (13865705372144903169/2500000000000000000)
  directionLo := (556807508997610921653/100000000000000000000)
  directionHi := (278403754498805460827/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree129.table
  base := (4992378684409438851947079673681459978457/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7310)
      previous := (5117)
      next := (0)
      square := (144160903099973531360511458070000000000000)
      linear := (-14833928208674988127868665774960000000000000)
      constant := (395623594105636792184440557827909419337740730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree129.table
  base := (12480946710799095098513764567712761515783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (65059)
      previous := (46784)
      next := (0)
      square := (1297448127899761782244603122630000000000000)
      linear := (-135693207583945079685583401161820000000000000)
      constant := (3674098015015717555937182801415603570810206332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell021.Kernel129
