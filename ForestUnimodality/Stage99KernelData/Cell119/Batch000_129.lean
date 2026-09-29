import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell119.Parameters
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch000_049
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch050_099
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch100_149
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch000_049
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch050_099
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree000.table
  base := (5992585862572714410333674081/100000000000000000000000000)
  polynomial :=
    { denominator := 500000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (39374848133409912076530190500000000000)
      linear := (-2299160996968843163890117150000000000)
      constant := (29962929312863572051668370405000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree000.table
  base := (5992585862572714410333674081/100000000000000000000000000)
  polynomial :=
    { denominator := 500000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (39374848133409912076530190500000000000)
      linear := (-2299160996968843163890117150000000000)
      constant := (29962929312863572051668370405000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree001.table
  base := (329105182183107521476795085402050233364611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-1902006766281707584614907998118577000000000000)
      constant := (718477481116339308583141986680071915541666470219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree001.table
  base := (164407732224920436379951389749772577752041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-951972660652404566309737917248763500000000000)
      constant := (358923263575642963332576146361303572770832250689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12484442801072604411/25000000000000000000)
  directionHi := (9987554240858083529/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree002.table
  base := (191149639613071956640048591728195892613239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-3703699804752286300060255128714707000000000000)
      constant := (418993206922540651988253312056423706416666662431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree002.table
  base := (19085478302899299306193113369163684847493/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6544587000000000000000000000000000000000000000
      center := (78535044)
      previous := (39267522)
      next := (39267522)
      square := (515384238441777552494404979707647000000000000)
      linear := (-1112273074439546818820817240441782100000000000)
      constant := (125506245067710003554848756420851297924999670391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12484442801072604411/25000000000000000000)
  centralHi := (9987554240858083529/20000000000000000000)
  directionLo := (70622673311792116403/100000000000000000000)
  directionHi := (17655668327948029101/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree003.table
  base := (118846073555618745479561918784141764915141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-5505392843222865015505602259310837000000000000)
      constant := (263675383898120783590845434045794731273562630589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree003.table
  base := (118615622886258336259019227344108180785561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-5511208508292169659519305768447687000000000000)
      constant := (263181972540701080042741801572497721520944102769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70622673311792116403/100000000000000000000)
  centralHi := (17655668327948029101/25000000000000000000)
  directionLo := (8649475694258104387/10000000000000000000)
  directionHi := (86494756942581043871/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree004.table
  base := (79434833788403206190133412193318694849997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-7307085881693443730950949389906967000000000000)
      constant := (181057885053178332037098592777722457057419105413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree004.table
  base := (39634472870595186443410422704967791877541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-3657420050892924961484610367711383500000000000)
      constant := (90356247522692447134532199533134526046820140189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8649475694258104387/10000000000000000000)
  centralHi := (86494756942581043871/100000000000000000000)
  directionLo := (12484442801072604411/12500000000000000000)
  directionHi := (99875542408580835289/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree005.table
  base := (14185147082103403757629037084874786452721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-2277194730041005611599074130125774250000000000)
      constant := (33963438645536428661373532055655410515417990409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree005.table
  base := (28311462895137972782222596227004535417901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32722935000000000000000000000000000000000000000
      center := (392675220)
      previous := (196337610)
      next := (196337610)
      square := (2576921192208887762472024898538235000000000000)
      linear := (-13677707542919295279628703553596770500000000000)
      constant := (203434170279658799730729496714087396437034451887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12484442801072604411/12500000000000000000)
  centralHi := (99875542408580835289/100000000000000000000)
  directionLo := (27916062764406227853/25000000000000000000)
  directionHi := (111664251057624911413/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree006.table
  base := (42734051372644289998684247679075795974009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-10910471958634601161841643651099227000000000000)
      constant := (110546872656477748963834525405606149115383879761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree006.table
  base := (42648697701703042482556817745749627921841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-10922103288773210449869050669372927000000000000)
      constant := (110397625405421470386599841305036052050705874889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27916062764406227853/25000000000000000000)
  centralHi := (111664251057624911413/100000000000000000000)
  directionLo := (3822564323198829159/3125000000000000000)
  directionHi := (122322058342362533089/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree007.table
  base := (6679997214971412854261621768356527180461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89042000000000000000000000000000000000000000
      center := (1068504)
      previous := (534252)
      next := (534252)
      square := (7012030454990170782236802445002000000000000)
      linear := (-51886387743286448478722411353858600000000000)
      constant := (393379116956070747592605642363269146601304181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree007.table
  base := (33335345340151457228700472503259877091783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (5342520)
      previous := (2671260)
      next := (2671260)
      square := (35060152274950853911184012225010000000000000)
      linear := (-259708875148303892108550319109143000000000000)
      constant := (1965042874215566354951996798638338988003270943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3822564323198829159/3125000000000000000)
  centralHi := (122322058342362533089/100000000000000000000)
  directionLo := (132122923635394931437/100000000000000000000)
  directionHi := (66061461817697465719/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree008.table
  base := (13352163090785601906955130768088969974907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-7256929017787879296366168956145743500000000000)
      constant := (44454706527767447498528048927693720580388892803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree008.table
  base := (5330579701473001645264843726334924870111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13089174000000000000000000000000000000000000000
      center := (157070088)
      previous := (78535044)
      next := (78535044)
      square := (1030768476883555104988809959415294000000000000)
      linear := (-8717619885456342586061328361993852200000000000)
      constant := (53317660573938859980069938200379660550905139157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132122923635394931437/100000000000000000000)
  centralHi := (66061461817697465719/50000000000000000000)
  directionLo := (141245346623584232807/100000000000000000000)
  directionHi := (17655668327948029101/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree009.table
  base := (4319121092608316740914970892464104284481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-3263110214809267461635537008577523400000000000)
      constant := (17169531357532156369731101332851250555619551449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree009.table
  base := (269410501353645594635967302750307901207/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-816649903462712562010939778514908350000000000)
      constant := (4291862765778785854791974008191685681648822012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141245346623584232807/100000000000000000000)
  centralHi := (17655668327948029101/12500000000000000000)
  directionLo := (149813313612871252933/100000000000000000000)
  directionHi := (74906656806435626467/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree010.table
  base := (4378322711162930440013981414560294645149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-4529311028129229005905758043370936750000000000)
      constant := (21492448923219993488563057163168666266937252821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree010.table
  base := (3495304683797409061959696769717248676481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-3627325932549586300733742107454649400000000000)
      constant := (17198371976911210520547017579335423787954919449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149813313612871252933/100000000000000000000)
  centralHi := (74906656806435626467/50000000000000000000)
  directionLo := (78958549138963686213/50000000000000000000)
  directionHi := (157917098277927372427/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree011.table
  base := (3536254914534410917772887511527133279317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-4979734287746873684767094826019969250000000000)
      constant := (22148600387964307925734101416881567285695135693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree011.table
  base := (2822542329898205294307487540072848019877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13089174000000000000000000000000000000000000000
      center := (157070088)
      previous := (78535044)
      next := (78535044)
      square := (1030768476883555104988809959415294000000000000)
      linear := (-11964156753744967060271175302548996200000000000)
      constant := (53188565548204445565175627675643933403862755799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78958549138963686213/50000000000000000000)
  centralHi := (157917098277927372427/100000000000000000000)
  directionLo := (16562484995124562987/10000000000000000000)
  directionHi := (165624849951245629871/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree012.table
  base := (5653118592777008670714071126336236754651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-10860315094729036727256863217338003500000000000)
      constant := (46659431447653996356050024931545061231137041379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree012.table
  base := (5638745182109030487763374349048205944561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-10871946424867646015284270235611703500000000000)
      constant := (46701644364090660631191011760279635666032213769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16562484995124562987/10000000000000000000)
  centralHi := (165624849951245629871/100000000000000000000)
  directionLo := (172989513885162087741/100000000000000000000)
  directionHi := (86494756942581043871/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree013.table
  base := (8880121436624992055208686208922075221397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-23522323227928652169959073565272137000000000000)
      constant := (99888329163607770645430320831352891835658976013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree013.table
  base := (8854388091297943660475967146244209648827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-23547524443228972294018455438198487000000000000)
      constant := (100004812434520251768698226646276750430995916483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172989513885162087741/100000000000000000000)
  centralHi := (86494756942581043871/50000000000000000000)
  directionLo := (180053194659458191969/100000000000000000000)
  directionHi := (18005319465945819197/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree014.table
  base := (3393637148428731862710798774913076002437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2671260)
      previous := (1335630)
      next := (1335630)
      square := (17530076137475426955592006112505000000000000)
      linear := (-258408329248971743728616537712941500000000000)
      constant := (1103363174157597333031560448408698556704497677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree014.table
  base := (3382096296514058708856704421573210340323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667815000000000000000000000000000000000000000
      center := (8013780)
      previous := (4006890)
      next := (4006890)
      square := (52590228412426280866776018337515000000000000)
      linear := (-776055797042530180330664400158374500000000000)
      constant := (3314674793030240176148506885871220692684560849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180053194659458191969/100000000000000000000)
  centralHi := (18005319465945819197/10000000000000000000)
  directionLo := (186850030505560263907/100000000000000000000)
  directionHi := (46712507626390065977/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree015.table
  base := (994033177154866817706526410919010352179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-5425141860973961920169953565292879400000000000)
      constant := (23583429100838194597867652588090758734578701691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree015.table
  base := (989894033955959671380488033617102041647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-5430957526043266564183657074429729400000000000)
      constant := (23620337572053324385467766478227668999812138263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186850030505560263907/100000000000000000000)
  centralHi := (46712507626390065977/25000000000000000000)
  directionLo := (2417601952761663603/1250000000000000000)
  directionHi := (193408156220933088241/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree016.table
  base := (211558500074443024358954828847269715749/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-7231850585835097079073778739265131750000000000)
      constant := (32288827542708922853411373432139259822912800884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree016.table
  base := (3366409976353585752486642130640115363641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-28958419223710013084368200339123727000000000000)
      constant := (129376171669039576822738679840557232229128387089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2417601952761663603/1250000000000000000)
  centralHi := (193408156220933088241/100000000000000000000)
  directionLo := (199751084817161670577/100000000000000000000)
  directionHi := (99875542408580835289/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree017.table
  base := (399380150346197537934666645054425822531/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-6145819076362193406348092417531331400000000000)
      constant := (28353684230501497597665493620318237310200229899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree017.table
  base := (30943035117696583607760928904791934957/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 16361467500000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1288460596104443881236012449269117500000000000)
      linear := (-23071538112902770010863586479574105250000000000)
      constant := (106520415809058141707629964368461719063590844144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199751084817161670577/100000000000000000000)
  centralHi := (99875542408580835289/50000000000000000000)
  directionLo := (102949352691608718171/50000000000000000000)
  directionHi := (205898705383217436343/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree018.table
  base := (77795486265605161207603822174016881107/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (26178348)
      previous := (13089174)
      next := (13089174)
      square := (171794746147259184164801659902549000000000000)
      linear := (-3253078842028154574718580921825278700000000000)
      constant := (15569516597731249112117096420255516972624472603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree018.table
  base := (1526426188129353933619473388198676487/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-1628284120534868680563401513653694350000000000)
      constant := (7799677859068509798611171161274255562950215575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102949352691608718171/50000000000000000000)
  centralHi := (205898705383217436343/100000000000000000000)
  directionLo := (211868019935376349211/100000000000000000000)
  directionHi := (52967004983844087303/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree019.table
  base := (-9219750315536337373876756918274383759/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-8583120364688031115657789087212229250000000000)
      constant := (42721271282224080542636324160255551164980899912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree019.table
  base := (-308132870385804857152422608022546956963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-34369314004191053874717945240048967000000000000)
      constant := (171224744365164113800972336104036599159523463573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211868019935376349211/100000000000000000000)
  centralHi := (52967004983844087303/25000000000000000000)
  directionLo := (217673698145157370683/100000000000000000000)
  directionHi := (54418424536289342671/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree020.table
  base := (-620639166212970136659042167294298302997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-18067087248611351589038251739722523500000000000)
      constant := (93648126483284271728672829415147331717361257587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree020.table
  base := (-1252892595563970606281485281391317767587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (785350440)
      previous := (392675220)
      next := (392675220)
      square := (5153842384417775524944049797076470000000000000)
      linear := (-108518836793054202414503580621072141000000000000)
      constant := (563036633247592350072004277686546759825381098431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217673698145157370683/100000000000000000000)
  centralHi := (54418424536289342671/25000000000000000000)
  directionLo := (27916062764406227853/12500000000000000000)
  directionHi := (8933140084609992913/4000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree021.table
  base := (-83073776161534443220867029790672474471/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89042000000000000000000000000000000000000000
      center := (1068504)
      previous := (534252)
      next := (534252)
      square := (7012030454990170782236802445002000000000000)
      linear := (-154840275655890946504170818816494600000000000)
      constant := (836300544819458311668922527371594953820383045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree021.table
  base := (-521779262026169499012107881405146971029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1335630)
      previous := (667815)
      next := (667815)
      square := (8765038068737713477796003056252500000000000)
      linear := (-193758046893767420416417220275505750000000000)
      constant := (1047555824919786888388454084877750951702817891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27916062764406227853/12500000000000000000)
  centralHi := (8933140084609992913/4000000000000000000)
  directionLo := (228843616581046895971/100000000000000000000)
  directionHi := (57210904145261723993/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree022.table
  base := (-2815197435738840035368056243957797094649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-39737560574163860608967197740637307000000000000)
      constant := (223647847560573606622120739699380829861907461679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree022.table
  base := (-2824263885349299303183648170925756619891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-39780208784672094665067690140974207000000000000)
      constant := (224121577900644187579895696274274429086765806661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228843616581046895971/100000000000000000000)
  centralHi := (57210904145261723993/25000000000000000000)
  directionLo := (234228909067060420031/100000000000000000000)
  directionHi := (3659826704172819063/1562500000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree023.table
  base := (-1733826585972110781225778042261605210611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-20769626806317219662206272435616718500000000000)
      constant := (121767104790692785023154487814605293146500995781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree023.table
  base := (-3475639066461741739757797724532804453061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (785350440)
      previous := (392675220)
      next := (392675220)
      square := (5153842384417775524944049797076470000000000000)
      linear := (-124751521134497324785552815323847861000000000000)
      constant := (732168366361519329164508637504485384902954869193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234228909067060420031/100000000000000000000)
  centralHi := (3659826704172819063/1562500000000000000)
  directionLo := (47898627469102834941/20000000000000000000)
  directionHi := (119746568672757087353/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree024.table
  base := (-4043730985475661714051401557355741202253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-43340946651105018039857892001829567000000000000)
      constant := (264531952755332012889878078744385195250790215163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree024.table
  base := (-405075209052193316919892270040790145819/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (26178348)
      previous := (13089174)
      next := (13089174)
      square := (171794746147259184164801659902549000000000000)
      linear := (-4338747197165945519196752007492436700000000000)
      constant := (26510382909584666059698223516025117913981622749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47898627469102834941/20000000000000000000)
  centralHi := (119746568672757087353/50000000000000000000)
  directionLo := (244644116684725066177/100000000000000000000)
  directionHi := (122322058342362533089/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree025.table
  base := (-568930586467396187999451392667401626543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-11285659922393899188825809783106424250000000000)
      constant := (71655898677926019928725206430170926994098551506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree025.table
  base := (-2278803496378101774843227254298791110503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-22595551782576567727708717520949723500000000000)
      constant := (143623618895850789919498273713007587527495500913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244644116684725066177/100000000000000000000)
  centralHi := (122322058342362533089/50000000000000000000)
  directionLo := (124844428010726044111/50000000000000000000)
  directionHi := (249688856021452088223/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree026.table
  base := (-2498771727887731569991966158757849660619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-23472166364023087735374293131510913500000000000)
      constant := (154897205975619828785226097067767945487719493549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree026.table
  base := (-1000588684032062899510219029636327871879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13089174000000000000000000000000000000000000000
      center := (157070088)
      previous := (78535044)
      next := (78535044)
      square := (1030768476883555104988809959415294000000000000)
      linear := (-28196841095188089431320410005324716200000000000)
      constant := (186282987283620110362660109578461945081963031027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124844428010726044111/50000000000000000000)
  centralHi := (249688856021452088223/100000000000000000000)
  directionLo := (254633669836008702103/100000000000000000000)
  directionHi := (31829208729501087763/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree027.table
  base := (-5387712746989369470051519808572329056137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-48746025766516754186193933393617957000000000000)
      constant := (334032001457553503947564900941912814566494506527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree027.table
  base := (-1348109430374788569585302661935658503387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-12199591688035123995579316243962401750000000000)
      constant := (83691167254849438740059919845136923340764661277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254633669836008702103/100000000000000000000)
  centralHi := (31829208729501087763/12500000000000000000)
  directionLo := (64871067706935782903/25000000000000000000)
  directionHi := (259484270827743131613/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree028.table
  base := (-2863371332811547445564084169721092148521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2671260)
      previous := (1335630)
      next := (1335630)
      square := (17530076137475426955592006112505000000000000)
      linear := (-515793049030482988792237556369531500000000000)
      constant := (3666590953959738148646439673299244256455696559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree028.table
  base := (-5730871371631405916134352071164063238813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (5342520)
      previous := (2671260)
      next := (2671260)
      square := (35060152274950853911184012225010000000000000)
      linear := (-1032693843788452576444228162098463000000000000)
      constant := (7349303622565863367093513505724608740544806427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64871067706935782903/25000000000000000000)
  centralHi := (259484270827743131613/100000000000000000000)
  directionLo := (2113966778166318903/800000000000000000)
  directionHi := (66061461817697465719/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree029.table
  base := (-120373385744211675502112236759114250823/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (26178348)
      previous := (13089174)
      next := (13089174)
      square := (171794746147259184164801659902549000000000000)
      linear := (-5234941184345791161708462765481021700000000000)
      constant := (38566734322691867129814215283592923037581758165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree029.table
  base := (-12044544758596152001039816377937704537/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3272293500000000000000000000000000000000000000
      center := (39267522)
      previous := (19633761)
      next := (19633761)
      square := (257692119220888776247202489853823500000000000)
      linear := (-7860844490869178476382564236469965050000000000)
      constant := (57977472557071211198312092020321131001932719525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2113966778166318903/800000000000000000)
  centralHi := (66061461817697465719/25000000000000000000)
  directionLo := (67230782009019899011/25000000000000000000)
  directionHi := (53784625607215919209/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree030.table
  base := (-313344676169862133754334132487015702527/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-2707555244096424516626498739270317350000000000)
      constant := (20652443574338280501377711337779924871481976217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree030.table
  base := (-783754272785453237122194417392402898893/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-13552315383155384193166752469193711750000000000)
      constant := (103489771190175891436390380400882702392761705206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67230782009019899011/25000000000000000000)
  centralHi := (53784625607215919209/20000000000000000000)
  directionLo := (273520437601217867167/100000000000000000000)
  directionHi := (8547513675038058349/3125000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree031.table
  base := (-6474281161570604174439238507416590219951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-55952797920399069047975321916002477000000000000)
      constant := (441464246469301418186525410430747650354060514921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree031.table
  base := (-101203370287796056014148544652132919633/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-14003223281528804259029231210937481750000000000)
      constant := (110609360958564267577275070310967774483455058288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273520437601217867167/100000000000000000000)
  centralHi := (8547513675038058349/3125000000000000000)
  directionLo := (2780417428704074537/1000000000000000000)
  directionHi := (278041742870407453701/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree032.table
  base := (-830405888273148205447435339660231652439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-14438622739717411940855167261649651750000000000)
      constant := (117727049997606584237622253569698305006972801538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree032.table
  base := (-6645625560885161803064096517150191542987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (785350440)
      previous := (392675220)
      next := (392675220)
      square := (5153842384417775524944049797076470000000000000)
      linear := (-173449574158826691898700519432175021000000000000)
      constant := (1415838919294000833605769400647044011380257338631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2780417428704074537/1000000000000000000)
  centralHi := (278041742870407453701/100000000000000000000)
  directionLo := (56498138649433693123/20000000000000000000)
  directionHi := (17655668327948029101/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree033.table
  base := (-6775826337768911464928874119161210886883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-59556183997340226478866016177194737000000000000)
      constant := (501376292681104263969385535618350378775149015893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree033.table
  base := (-847236632322374063000163907655280286993/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-14905039078275644390754188694425021750000000000)
      constant := (125620311399838901779138005277326319601592895406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56498138649433693123/20000000000000000000)
  centralHi := (17655668327948029101/6250000000000000000)
  directionLo := (286870655111529120253/100000000000000000000)
  directionHi := (143435327555764560127/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree034.table
  base := (-6873733694289409290987547866419302016941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-61357877035810805194311363307790867000000000000)
      constant := (532864783572578518458084007108434719490284717211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree034.table
  base := (-6875527890120837549771193228434846554521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-61423787906596257826466669744675167000000000000)
      constant := (534038531581201400125378051432552905630762357391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286870655111529120253/100000000000000000000)
  centralHi := (143435327555764560127/50000000000000000000)
  directionLo := (291184741628008293203/100000000000000000000)
  directionHi := (72796185407002073301/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree035.table
  base := (-1387682848157913983752320335198571987707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89042000000000000000000000000000000000000000
      center := (1068504)
      previous := (534252)
      next := (534252)
      square := (7012030454990170782236802445002000000000000)
      linear := (-257794163568495444529619226279130600000000000)
      constant := (2307634776381841419996255156745775376535296653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree035.table
  base := (-6939970500506916620454542405926449552147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (16027560)
      previous := (8013780)
      next := (8013780)
      square := (105180456824852561733552036675030000000000000)
      linear := (-3871066500005506413668362329284709000000000000)
      constant := (34690715632918704006485769612458235618466590239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291184741628008293203/100000000000000000000)
  centralHi := (72796185407002073301/25000000000000000000)
  directionLo := (295435838634756705829/100000000000000000000)
  directionHi := (29543583863475670583/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree036.table
  base := (-1742771427900504810960086260167142693567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-16240315778187990656300514392245781750000000000)
      constant := (149722711520315308313750500938175418866845476057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree036.table
  base := (-6972434487104545686228471016115213408997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-65031051093583618353366499678625327000000000000)
      constant := (600208069370916779617116072372684066607084183587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295435838634756705829/100000000000000000000)
  centralHi := (29543583863475670583/10000000000000000000)
  directionLo := (149813313612871252933/50000000000000000000)
  directionHi := (299626627225742505867/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree037.table
  base := (-348638713703502939423729456192477181313/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-3338147807561127067032370234978962850000000000)
      constant := (31671176128094525464965409416595361147127432423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree037.table
  base := (-6973942325723179870675044176556527229019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-66834682687077298616816414645600407000000000000)
      constant := (634815443120305117832630698606316069710605409949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149813313612871252933/50000000000000000000)
  centralHi := (299626627225742505867/100000000000000000000)
  directionLo := (303759603528063154283/100000000000000000000)
  directionHi := (75939900882015788571/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree038.table
  base := (-3472172332649423980891619245486739755329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-34282324594846560028046375915087693500000000000)
      constant := (334483331603183347365692656191298433608296881959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree038.table
  base := (-6945355469616806703140751849460314905409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (785350440)
      previous := (392675220)
      next := (392675220)
      square := (5153842384417775524944049797076470000000000000)
      linear := (-205914942841712936640798988837726461000000000000)
      constant := (2011305791901744385774711190410832014054154028917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303759603528063154283/100000000000000000000)
  centralHi := (75939900882015788571/25000000000000000000)
  directionLo := (76959274022197194319/25000000000000000000)
  directionHi := (307837096088788777277/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree039.table
  base := (-6886525587581229917128275314829846728013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-70366342228163698771538098960771517000000000000)
      constant := (705518678329505585719722764297347372297284528123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree039.table
  base := (-6887399708017762413353796989308630916657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-70441945874064659143716244579550567000000000000)
      constant := (707065948581487582671032430101479589705016171447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76959274022197194319/25000000000000000000)
  centralHi := (307837096088788777277/100000000000000000000)
  directionLo := (77965320303817706413/25000000000000000000)
  directionHi := (311861281215270825653/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree040.table
  base := (-664055772323349447351894950006454341/976562500000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-3608401763331713874349172304568382350000000000)
      constant := (37153911416243431032228970122585612269981496832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree040.table
  base := (-3400343265478057121140191728929445709453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-36122788733779169703583079773262823500000000000)
      constant := (372353081489894838756449518377793515230902706363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77965320303817706413/25000000000000000000)
  centralHi := (311861281215270825653/100000000000000000000)
  directionLo := (78958549138963686213/25000000000000000000)
  directionHi := (315834196555854744853/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree041.table
  base := (-6685078694954309569970809120445318571179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-73969728305104856202428793221963777000000000000)
      constant := (781644184324004961757125712339515696622734447309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree041.table
  base := (-1337146225881704970760018303817671358669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13089174000000000000000000000000000000000000000
      center := (157070088)
      previous := (78535044)
      next := (78535044)
      square := (1030768476883555104988809959415294000000000000)
      linear := (-44429525436631211802369644708100436200000000000)
      constant := (470012869954858971115619795947343366855782525297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78958549138963686213/25000000000000000000)
  centralHi := (315834196555854744853/100000000000000000000)
  directionLo := (159878876580784075139/50000000000000000000)
  directionHi := (319757753161568150279/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree042.table
  base := (-3271202204431480110895327982325348732437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2671260)
      previous := (1335630)
      next := (1335630)
      square := (17530076137475426955592006112505000000000000)
      linear := (-773177768811994233855858575026121500000000000)
      constant := (8379750969842823946078584968304703649083172323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree042.table
  base := (-3271483780351593614895710057396580545537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2671260)
      previous := (1335630)
      next := (1335630)
      square := (17530076137475426955592006112505000000000000)
      linear := (-774008578107609183000673362045671500000000000)
      constant := (8398070025589431532682345710749364837532147223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159878876580784075139/50000000000000000000)
  centralHi := (319757753161568150279/100000000000000000000)
  directionLo := (323633746231425012737/100000000000000000000)
  directionHi := (161816873115712506369/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree043.table
  base := (-99566808032002328263905536545877974727/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-19393278595511503408329871870789009250000000000)
      constant := (215447914713464533869255570246850245632748518672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree043.table
  base := (-6372761525626816264057340874815950149973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-77656472248039380197515904447450887000000000000)
      constant := (863673602941916151187846593082504461085279551283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323633746231425012737/100000000000000000000)
  centralHi := (161816873115712506369/50000000000000000000)
  directionLo := (163731932356396549113/50000000000000000000)
  directionHi := (327463864712793098227/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree044.table
  base := (-308750113360088639174593351730891033529/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-3968740371025829617438241730687608350000000000)
      constant := (45168585011336785549647751525957945914516514159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree044.table
  base := (-3087710566679690777944706098919899311103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32722935000000000000000000000000000000000000000
      center := (392675220)
      previous := (196337610)
      next := (196337610)
      square := (2576921192208887762472024898538235000000000000)
      linear := (-119190155762299590691448729121638950500000000000)
      constant := (1358013498617163897371485329146277564927246350539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163731932356396549113/50000000000000000000)
  centralHi := (327463864712793098227/100000000000000000000)
  directionLo := (16562484995124562987/5000000000000000000)
  directionHi := (331249699902491259741/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree045.table
  base := (-297542250588373971037672952687447756949/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-4058825022949358553210509087217414850000000000)
      constant := (47297757495376989777902802931613514282230804979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree045.table
  base := (-5951205971122863375923966775807862184267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-81263735435026740724415734381401047000000000000)
      constant := (948016484619290851984479750477357440217018195757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16562484995124562987/5000000000000000000)
  centralHi := (331249699902491259741/100000000000000000000)
  directionLo := (83748188293218683559/25000000000000000000)
  directionHi := (334992753172874734237/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree046.table
  base := (-1425005960290536942786239139098669994923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-20744548374364437444913882218736106750000000000)
      constant := (247385382048101139717634475830498614294645622733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree046.table
  base := (-1140066949104671753262654753438530455789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-16613473405704084197573129869675225400000000000)
      constant := (198339116490131444024809157727401654493313078619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83748188293218683559/25000000000000000000)
  centralHi := (334992753172874734237/100000000000000000000)
  directionLo := (338694442929308529497/100000000000000000000)
  directionHi := (169347221464654264749/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree047.table
  base := (-1355681014118901397843993447801290583167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-21194971633982082123775219001385139250000000000)
      constant := (258532607710407202518533399131521970605394277657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree047.table
  base := (-271149586025998950237525823403181471949/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3272293500000000000000000000000000000000000000
      center := (39267522)
      previous := (19633761)
      next := (19633761)
      square := (257692119220888776247202489853823500000000000)
      linear := (-12730649793302115187697334647302681050000000000)
      constant := (155456883589255686989976040217066963880041709937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338694442929308529497/100000000000000000000)
  centralHi := (169347221464654264749/50000000000000000000)
  directionLo := (171178055445234195607/50000000000000000000)
  directionHi := (68471222178093678243/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree048.table
  base := (-511910180829273842191343391162366069231/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (26178348)
      previous := (13089174)
      next := (13089174)
      square := (171794746147259184164801659902549000000000000)
      linear := (-8658157957439890721054622313613668700000000000)
      constant := (107972151720818325440063387184454264311356565801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree048.table
  base := (-5119332141530353990374592691544527541917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-86674630215507781514765479282326287000000000000)
      constant := (1082067070380052254675624608300305894376009348907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171178055445234195607/50000000000000000000)
  centralHi := (68471222178093678243/20000000000000000000)
  directionLo := (345979027770324175483/100000000000000000000)
  directionHi := (86494756942581043871/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree049.table
  base := (-4789288682448409238193129880705249740203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (5342520)
      previous := (2671260)
      next := (2671260)
      square := (35060152274950853911184012225010000000000000)
      linear := (-1803740257405499712775338168708833000000000000)
      constant := (22986010208852105082818352230417513576316422237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree049.table
  base := (-2394743402668948409361130765558967591393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2671260)
      previous := (1335630)
      next := (1335630)
      square := (17530076137475426955592006112505000000000000)
      linear := (-902839406214300630389953002543891500000000000)
      constant := (11517947310905348183311281619062660203863592247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345979027770324175483/100000000000000000000)
  centralHi := (86494756942581043871/25000000000000000000)
  directionLo := (349564398430032923511/100000000000000000000)
  directionHi := (43695549803754115439/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree050.table
  base := (-4433395564385288002130811202847283400651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-90184965651340064641436917397328947000000000000)
      constant := (1173909138018529631687181655763255993690261224621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree050.table
  base := (-4433565910321495555240810159647945108957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (785350440)
      previous := (392675220)
      next := (392675220)
      square := (5153842384417775524944049797076470000000000000)
      linear := (-270845680207485426124995927648829341000000000000)
      constant := (3529362845380282653491868252835059433863206434241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349564398430032923511/100000000000000000000)
  centralHi := (43695549803754115439/12500000000000000000)
  directionLo := (353113366558960582019/100000000000000000000)
  directionHi := (17655668327948029101/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree051.table
  base := (-2025757947799673489703204419091646358857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-45993329344905321678441132263962538500000000000)
      constant := (611252613358589717703552293577703493310409047647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree051.table
  base := (-810332460068739597295472474689735463503/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-18417104999197764461023044836650305400000000000)
      constant := (245030640762516784452747540940538776484039763913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353113366558960582019/100000000000000000000)
  centralHi := (17655668327948029101/5000000000000000000)
  directionLo := (89156754734097025783/25000000000000000000)
  directionHi := (356627018936388103133/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree052.table
  base := (-3643728417805194641265323199709341239363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-93788351728281222072327611658521207000000000000)
      constant := (1272102594552368632114200546349348254515433673973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree052.table
  base := (-455481774723135154679889403871310302607/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-23472289147370625642141284787556651750000000000)
      constant := (318713857970450389307227658587359694613728107794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89156754734097025783/25000000000000000000)
  centralHi := (356627018936388103133/100000000000000000000)
  directionLo := (180053194659458191969/50000000000000000000)
  directionHi := (360106389318916383939/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree053.table
  base := (-3210099485409289416763983884023050470031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-95590044766751800787772958789117337000000000000)
      constant := (1322701096770035254958188489543643784731163742601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree053.table
  base := (-3210207506174933685121559463448951753001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (785350440)
      previous := (392675220)
      next := (392675220)
      square := (5153842384417775524944049797076470000000000000)
      linear := (-287078364548928548496045162351605061000000000000)
      constant := (3976682466691860333347088831957498553193682444413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180053194659458191969/50000000000000000000)
  centralHi := (360106389318916383939/100000000000000000000)
  directionLo := (181776230996491282981/50000000000000000000)
  directionHi := (363552461992982565963/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree054.table
  base := (-1375342507100789405452794455750240317537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-48695868902611189751609152959856733500000000000)
      constant := (687150305694130987774213147582050305490323825927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree054.table
  base := (-1375388875099479829948701819323131217513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-48748209888234931547732484542088383500000000000)
      constant := (688634626865163752020980494531377222878190082623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181776230996491282981/50000000000000000000)
  centralHi := (363552461992982565963/100000000000000000000)
  directionLo := (183483087513543799633/50000000000000000000)
  directionHi := (366966175027087599267/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree055.table
  base := (-14159575771830894172855770659516688307/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-4959671542184647910933182652515479850000000000)
      constant := (71345051780745282430858667332272365997794548776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree055.table
  base := (-566402927547625803341412521083763930659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-24825012842490885839728721012787961750000000000)
      constant := (357495156082067479073041012407775010056113402389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183483087513543799633/50000000000000000000)
  centralHi := (366966175027087599267/100000000000000000000)
  directionLo := (46293552906773494711/12500000000000000000)
  directionHi := (370348423254187957689/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree056.table
  base := (-1754680519923250647280677936006205258417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (5342520)
      previous := (2671260)
      next := (2671260)
      square := (35060152274950853911184012225010000000000000)
      linear := (-2061124977187010957838959187365423000000000000)
      constant := (30214332302628161399228188494631135735690016743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree056.table
  base := (-27417949987790090390909271786515148289/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 333907500000000000000000000000000000000000000
      center := (4006890)
      previous := (2003445)
      next := (2003445)
      square := (26295114206213140433388009168757500000000000)
      linear := (-1547505351481488116668848964563167250000000000)
      constant := (22709615021076954217729777740349558835985220688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46293552906773494711/12500000000000000000)
  centralHi := (370348423254187957689/100000000000000000000)
  directionLo := (186850030505560263907/50000000000000000000)
  directionHi := (74740012202224105563/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree057.table
  base := (-30454091589461903226159846925135284721/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-5139840846031705782477717365575092850000000000)
      constant := (76755214001786842967275533063439747294915763182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree057.table
  base := (-30455555582723440387534972009121838701/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-5145365727847545194290735699255100350000000000)
      constant := (76920592621834627284130912630293609588680892342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186850030505560263907/50000000000000000000)
  centralHi := (74740012202224105563/20000000000000000000)
  directionLo := (188510952329411925653/50000000000000000000)
  directionHi := (377021904658823851307/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree058.table
  base := (-656009750662401328264655916470477451529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-104598509959104694364999694442097987000000000000)
      constant := (1590706965724940261027388937019183016795643392159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree058.table
  base := (-656059958951038071720746520929774677261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-104710946150444584149264628952077087000000000000)
      constant := (1594131576475741540122916425508161945578089487931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188510952329411925653/50000000000000000000)
  centralHi := (377021904658823851307/100000000000000000000)
  directionLo := (23769670931526254851/6250000000000000000)
  directionHi := (380314734904420077617/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree059.table
  base := (-6824254158117666488881279526982573219/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (26178348)
      previous := (13089174)
      next := (13089174)
      square := (171794746147259184164801659902549000000000000)
      linear := (-10640020299757527308044504157269411700000000000)
      constant := (164731028806237504468832565456277191534028128149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree059.table
  base := (-68285576664653867075270149196653366619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (785350440)
      previous := (392675220)
      next := (392675220)
      square := (5153842384417775524944049797076470000000000000)
      linear := (-319543733231814793238143631757156501000000000000)
      constant := (4952561906223206597270435950592029615933319058647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23769670931526254851/6250000000000000000)
  centralHi := (380314734904420077617/100000000000000000000)
  directionLo := (38357929894387076599/10000000000000000000)
  directionHi := (383579298943870765991/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree060.table
  base := (545117941240744580098355525963083716677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-108201896036045851795890388703290247000000000000)
      constant := (1704914203368541615186711730914820890057358659133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree060.table
  base := (272540532565321286177989948799840272091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-54159104668715972338082229443013623500000000000)
      constant := (854289492955478165584606561035139226748934407139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38357929894387076599/10000000000000000000)
  centralHi := (383579298943870765991/100000000000000000000)
  directionLo := (2417601952761663603/625000000000000000)
  directionHi := (386816312441866176481/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree061.table
  base := (1184054825320390357947040120547770900437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-110003589074516430511335735833886377000000000000)
      constant := (1763518674835629066992010044157317600104659428173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree061.table
  base := (1184023235518406317994834670508401690117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-110121840930925624939614373853002327000000000000)
      constant := (1767306591486424515171523636797931945030639248893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2417601952761663603/625000000000000000)
  centralHi := (386816312441866176481/100000000000000000000)
  directionLo := (97506615340952473177/25000000000000000000)
  directionHi := (390026461363809892709/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree062.table
  base := (1848553892582653012696610872297589497377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-111805282112987009226781082964482507000000000000)
      constant := (1823123671446494228574620456833527507118623349433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree062.table
  base := (924263419276069205348020271799283155229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32722935000000000000000000000000000000000000000
      center := (392675220)
      previous := (196337610)
      next := (196337610)
      square := (2576921192208887762472024898538235000000000000)
      linear := (-167888208786628957804596433229966110500000000000)
      constant := (2740555132075136021753847512574470261147030695423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97506615340952473177/25000000000000000000)
  centralHi := (390026461363809892709/100000000000000000000)
  directionLo := (393210403673183027113/100000000000000000000)
  directionHi := (196605201836591513557/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree063.table
  base := (253860316178080003316064961244209846899/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (534252)
      previous := (267126)
      next := (267126)
      square := (3506015227495085391118401222501000000000000)
      linear := (-231850969696852220290258020602201300000000000)
      constant := (3844345238905509993481932598575818366593790379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree063.table
  base := (101543199931503844065174254245565934397/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89042000000000000000000000000000000000000000
      center := (1068504)
      previous := (534252)
      next := (534252)
      square := (7012030454990170782236802445002000000000000)
      linear := (-464200424971073410067404913416132600000000000)
      constant := (7705181427323420658051936121046101004826444185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393210403673183027113/100000000000000000000)
  centralHi := (196605201836591513557/50000000000000000000)
  directionLo := (396368770906184794313/100000000000000000000)
  directionHi := (198184385453092397157/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree064.table
  base := (3254192536607926607482183490251796713393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-115408668189928166657671777225674767000000000000)
      constant := (1945335139661859765939284063437108999832371517897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree064.table
  base := (1627086354582708565455891447634721576521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-57766367855703332864982059376963783500000000000)
      constant := (974752327295724372670280680614021430526106280609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396368770906184794313/100000000000000000000)
  centralHi := (198184385453092397157/50000000000000000000)
  directionLo := (79900433926864668231/20000000000000000000)
  directionHi := (99875542408580835289/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree065.table
  base := (15606693395177019628552282017682232081/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-29302590307099686343279281089067724250000000000)
      constant := (501985392670186514647067750494715167332443638336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree065.table
  base := (998824135363137120107021810036862834327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16361467500000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1288460596104443881236012449269117500000000000)
      linear := (-88002275478675259495060525290676985250000000000)
      constant := (1509181763264011712078890102854739744526319637949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79900433926864668231/20000000000000000000)
  centralHi := (99875542408580835289/25000000000000000000)
  directionLo := (402611182824550614729/100000000000000000000)
  directionHi := (40261118282455061473/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree066.table
  base := (95239178201587104790134141498932229899/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (26178348)
      previous := (13089174)
      next := (13089174)
      square := (171794746147259184164801659902549000000000000)
      linear := (-11901205426686932408856247148686702700000000000)
      constant := (207154844448016231951403406612884878342796677855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree066.table
  base := (4761944393071695840095252679101085295843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-119139998898394026256863948687877727000000000000)
      constant := (2075982523482551095737619584027127843504355083947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402611182824550614729/100000000000000000000)
  centralHi := (40261118282455061473/10000000000000000000)
  directionLo := (25356023194098695343/6250000000000000000)
  directionHi := (405696371105579125489/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree067.table
  base := (5554122697928559659651180973165575026917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-120813747305339902804007818617463157000000000000)
      constant := (2136155747880572385401481587252066902722895216093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree067.table
  base := (2777055140256750638140726437461535320103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-60471815245943853260156931827426403500000000000)
      constant := (1070362579464927999067130898706442982685328977487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25356023194098695343/6250000000000000000)
  centralHi := (405696371105579125489/100000000000000000000)
  directionLo := (408758273948170784141/100000000000000000000)
  directionHi := (204379136974085392071/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree068.table
  base := (1592949945449186063496229026392302533353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-30653860085952620379863291437014821750000000000)
      constant := (550440867443998739963452854850598394853283036737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree068.table
  base := (127435783253532160145504334110782537709/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6544587000000000000000000000000000000000000000
      center := (78535044)
      previous := (39267522)
      next := (39267522)
      square := (515384238441777552494404979707647000000000000)
      linear := (-36824178625614416035129133586548366100000000000)
      constant := (661941073908986456460938960023437932580586655915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408758273948170784141/100000000000000000000)
  centralHi := (204379136974085392071/50000000000000000000)
  directionLo := (102949352691608718171/25000000000000000000)
  directionHi := (82359482153286974537/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree069.table
  base := (1803746467935282343826605470562784538281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-31104283345570265058724628219663854250000000000)
      constant := (567092900201948865182510935503680235291011611649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree069.table
  base := (3607488396225023786768258054693221605137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-62275446839437533523606846794401483500000000000)
      constant := (1136608888258825961015825947072868108035032914473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102949352691608718171/25000000000000000000)
  centralHi := (82359482153286974537/20000000000000000000)
  directionLo := (5185178524331273399/1250000000000000000)
  directionHi := (414814281946501871921/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree070.table
  base := (8083677352784010107781192071574312125349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (5342520)
      previous := (2671260)
      next := (2671260)
      square := (35060152274950853911184012225010000000000000)
      linear := (-2575894416750033447966201224678603000000000000)
      constant := (47673063940608065110262102460082694950132662829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree070.table
  base := (8083669591669017763639322492142257657981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (5342520)
      previous := (2671260)
      next := (2671260)
      square := (35060152274950853911184012225010000000000000)
      linear := (-2578663781068749945115583848077103000000000000)
      constant := (47774851869124018710537507487395325453190972101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5185178524331273399/1250000000000000000)
  centralHi := (414814281946501871921/100000000000000000000)
  directionLo := (417809369808342146587/100000000000000000000)
  directionHi := (104452342452085536647/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree071.table
  base := (8977871178727412027829733859087871742449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-128020519459222217665789207139847677000000000000)
      constant := (2404589059976624927925912307610370742754433024521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree071.table
  base := (897786454576314792755487289006621367779/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6544587000000000000000000000000000000000000000
      center := (78535044)
      previous := (39267522)
      next := (39267522)
      square := (515384238441777552494404979707647000000000000)
      linear := (-38447447059758728272234057056825938100000000000)
      constant := (722916040498557145933020356314551529717488662273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417809369808342146587/100000000000000000000)
  centralHi := (104452342452085536647/25000000000000000000)
  directionLo := (420783139505964596207/100000000000000000000)
  directionHi := (26298946219122787263/6250000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree072.table
  base := (9897564782672311397146491027238664541567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-129822212497692796381234554270443807000000000000)
      constant := (2474198375868520012942449621463954500618700115943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree072.table
  base := (1237194889374503083201671794131539679891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-32490447114839026959390859622432051750000000000)
      constant := (619868737800370998181368403224871723252665866678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420783139505964596207/100000000000000000000)
  centralHi := (26298946219122787263/6250000000000000000)
  directionLo := (423736039870752698423/100000000000000000000)
  directionHi := (52967004983844087303/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree073.table
  base := (10842756001614564889961251048129500684519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-131623905536163375096679901401039937000000000000)
      constant := (2544808076046824179667130796139032297498798049551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree073.table
  base := (1084275115968313875797901414407996588651/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (26178348)
      previous := (13089174)
      next := (13089174)
      square := (171794746147259184164801659902549000000000000)
      linear := (-13176542005284978810101335345670328700000000000)
      constant := (255023218553817362794871594171093650990043227379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423736039870752698423/100000000000000000000)
  centralHi := (52967004983844087303/12500000000000000000)
  directionLo := (426668504202267287233/100000000000000000000)
  directionHi := (213334252101133643617/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree074.table
  base := (118134430129030895123422393534811114171/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-6671279928731697690606262426581803350000000000)
      constant := (130820907826768561683364342069672021425431737295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree074.table
  base := (5906719438593444927366157791219589222923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32722935000000000000000000000000000000000000000
      center := (392675220)
      previous := (196337610)
      next := (196337610)
      square := (2576921192208887762472024898538235000000000000)
      linear := (-200353577469515202546694902635517550500000000000)
      constant := (3932987751109129785689053032158592079773681967801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426668504202267287233/100000000000000000000)
  centralHi := (213334252101133643617/50000000000000000000)
  directionLo := (214790475505230582241/50000000000000000000)
  directionHi := (429580951010461164483/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree075.table
  base := (6404812140347098297054673476045243901259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-67613645806552266263785297831116098500000000000)
      constant := (1344514306991836814320974207119854392382669645011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree075.table
  base := (12809620748833961144722622302497692313089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-135372683239837148627913183390653447000000000000)
      constant := (2694753893492192798107719171853200138214080733081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214790475505230582241/50000000000000000000)
  centralHi := (429580951010461164483/100000000000000000000)
  directionLo := (216236892356452609677/50000000000000000000)
  directionHi := (86494756942581043871/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree076.table
  base := (6915649255414772508635485792436795116663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-68514492325787555621507971396414163500000000000)
      constant := (1381319722784243706425162206296590010214058717727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree076.table
  base := (13831295495192456768451518693274024865283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-137176314833330828891363098357628527000000000000)
      constant := (2768518361005374666551291673843943942190335957707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216236892356452609677/50000000000000000000)
  centralHi := (86494756942581043871/20000000000000000000)
  directionLo := (217673698145157370683/50000000000000000000)
  directionHi := (435347396290314741367/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree077.table
  base := (2975692922562511843150128162662200810897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89042000000000000000000000000000000000000000
      center := (1068504)
      previous := (534252)
      next := (534252)
      square := (7012030454990170782236802445002000000000000)
      linear := (-566655827306308938605964448667038600000000000)
      constant := (11580614893513725233854398349434789042301945337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree077.table
  base := (14878462038392277873926963890326054057579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (16027560)
      previous := (8013780)
      next := (8013780)
      square := (105180456824852561733552036675030000000000000)
      linear := (-8508976311846398519682429387220629000000000000)
      constant := (174078687811891464300710133622224116758092423977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217673698145157370683/50000000000000000000)
  centralHi := (435347396290314741367/100000000000000000000)
  directionLo := (109550540975846054543/25000000000000000000)
  directionHi := (438202163903384218173/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree078.table
  base := (3190224333553324354570164231222522580581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-28126474145703253734781327410804117400000000000)
      constant := (582572444401248689731505441955366664662692288349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree078.table
  base := (15951119470379542687052794382457413257607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-140783578020318189418262928291578687000000000000)
      constant := (2919054511277804672535878468321933334286454141103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109550540975846054543/25000000000000000000)
  centralHi := (438202163903384218173/100000000000000000000)
  directionLo := (220519226736842871537/50000000000000000000)
  directionHi := (17641538138947429723/4000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree079.table
  base := (426231722535850516022794088047506006093/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-7121703188349342369467599209230835850000000000)
      constant := (149473708158278202981715206515677245109932112394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree079.table
  base := (17049267026170534774425231231211566899373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-142587209613811869681712843258553767000000000000)
      constant := (2995826190387272771496883618856930076326422281317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220519226736842871537/50000000000000000000)
  centralHi := (17641538138947429723/4000000000000000000)
  directionLo := (55482077403894657543/12500000000000000000)
  directionHi := (88771323846231452069/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree080.table
  base := (9086452830711333016780933892153953543257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-72117878402728713052398665657606423500000000000)
      constant := (1533543235482806125992542453384793502119267899953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree080.table
  base := (9086452030658916850849147283539753001601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32722935000000000000000000000000000000000000000
      center := (392675220)
      previous := (196337610)
      next := (196337610)
      square := (2576921192208887762472024898538235000000000000)
      linear := (-216586261810958324917744137338293270500000000000)
      constant := (4610400405275126215712843924473851021477488883787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55482077403894657543/12500000000000000000)
  centralHi := (88771323846231452069/20000000000000000000)
  directionLo := (446657004230499645649/100000000000000000000)
  directionHi := (8933140084609992913/2000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree081.table
  base := (19322031398032339254251436405030100066887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-146037449843928004820242678445808977000000000000)
      constant := (3145699144207201057317004174023917541168815930223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree081.table
  base := (1207626877057829729235605454361655563557/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-36548618200199807552153168298125981750000000000)
      constant := (788094187370473766037515141891087327899643754612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446657004230499645649/100000000000000000000)
  centralHi := (8933140084609992913/2000000000000000000)
  directionLo := (1123599852096534397/250000000000000000)
  directionHi := (449439940838613758801/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree082.table
  base := (10248322824048679295671594370304790911269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-73919571441199291767844012788202553500000000000)
      constant := (1612656090939960554585677783435847944711869750301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree082.table
  base := (20496644483652858325305449188226794060199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-147998104394292910472062588159479007000000000000)
      constant := (3232155627285005054540600365847794453819351864271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1123599852096534397/250000000000000000)
  centralHi := (449439940838613758801/100000000000000000000)
  directionLo := (45220575119503808983/10000000000000000000)
  directionHi := (452205751195038089831/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree083.table
  base := (10848374010685566543584561578999361778193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-74820417960434581125566686353500618500000000000)
      constant := (1652962791566219076111424283689190644200619597097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree083.table
  base := (10848373514120359495178633252666618377261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32722935000000000000000000000000000000000000000
      center := (392675220)
      previous := (196337610)
      next := (196337610)
      square := (2576921192208887762472024898538235000000000000)
      linear := (-224702603981679886103268754689681130500000000000)
      constant := (4969405354128437827998696395109805024965783436207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45220575119503808983/10000000000000000000)
  centralHi := (452205751195038089831/100000000000000000000)
  directionLo := (454954747647192654327/100000000000000000000)
  directionHi := (56869343455899081791/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree084.table
  base := (22922338189052724985196352299288482226249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (5342520)
      previous := (2671260)
      next := (2671260)
      square := (35060152274950853911184012225010000000000000)
      linear := (-3090663856313055938093443261991783000000000000)
      constant := (69133456066274763378130851884060444517194831729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree084.table
  base := (11461168671077734816732445625579060685163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2671260)
      previous := (1335630)
      next := (1335630)
      square := (17530076137475426955592006112505000000000000)
      linear := (-1546993546747757867336351205034991500000000000)
      constant := (34640005869140577133378896683132081360764141923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454954747647192654327/100000000000000000000)
  centralHi := (56869343455899081791/12500000000000000000)
  directionLo := (457687233162093791943/100000000000000000000)
  directionHi := (57210904145261723993/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree085.table
  base := (24173415874118448235033310630790421778037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-153244221997810319682024066968193497000000000000)
      constant := (3470153473620661664282220430126295568031019278573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree085.table
  base := (24173415152024648257883425955394197958479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-153408999174773951262412333060404247000000000000)
      constant := (3477506643959089122109306301035514419278162734391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457687233162093791943/100000000000000000000)
  centralHi := (57210904145261723993/12500000000000000000)
  directionLo := (460403501716076074087/100000000000000000000)
  directionHi := (57550437714509509261/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree086.table
  base := (1590623802698408811185235737199838684993/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-38761478759070224599367353524697406750000000000)
      constant := (888441990435719417143143202307838199296536377188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree086.table
  base := (6362495056894420894587726272250842429513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16361467500000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1288460596104443881236012449269117500000000000)
      linear := (-116409473076200723644396686020534495250000000000)
      constant := (2670971331449915734006215968455238303103239196131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460403501716076074087/100000000000000000000)
  centralHi := (57550437714509509261/12500000000000000000)
  directionLo := (463103838663940380997/100000000000000000000)
  directionHi := (231551919331970190499/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree087.table
  base := (668800822489790530701322185309745822661/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-7842380403737573855645738061469287850000000000)
      constant := (181919140559257935966926491439114972439527657338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree087.table
  base := (83600101171425368021516488658112160223/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-7850813118088065589465608149717720350000000000)
      constant := (182304298433752306411052849356499301904465935472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463103838663940380997/100000000000000000000)
  centralHi := (231551919331970190499/50000000000000000000)
  directionLo := (465788521088840250689/100000000000000000000)
  directionHi := (46578852108884025069/10000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree088.table
  base := (28079571877719278832905724910776417186363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-158649301113222055828360108359981887000000000000)
      constant := (3723998021586133642977292110921164642608149289027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree088.table
  base := (14039785715246597935472324735534481269007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-79409946977627496026381038980664743500000000000)
      constant := (1865939611914087628591374815568381009388295571703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465788521088840250689/100000000000000000000)
  centralHi := (46578852108884025069/10000000000000000000)
  directionLo := (234228909067060420031/50000000000000000000)
  directionHi := (468457818134120840063/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree089.table
  base := (7358149409502719715540922941976069055037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-40112748537923158635951363872644504250000000000)
      constant := (952653398160344352133421969165258558949565811573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree089.table
  base := (14716298628447205095610790219671066000947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32722935000000000000000000000000000000000000000
      center := (392675220)
      previous := (196337610)
      next := (196337610)
      square := (2576921192208887762472024898538235000000000000)
      linear := (-240935288323123008474317989392456850500000000000)
      constant := (5728012310638662935159905131598233639825939723889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234228909067060420031/50000000000000000000)
  centralHi := (468457818134120840063/100000000000000000000)
  directionLo := (94222398263647077137/20000000000000000000)
  directionHi := (235555995659117692843/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree090.table
  base := (15405555031457691605143314815494504032771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-81126343595081606629625401310587073500000000000)
      constant := (1949114762047224508700188104945358412388106886859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree090.table
  base := (30811109738177110081118775254818564872737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-162427157142242352579661907895279647000000000000)
      constant := (3906472918215044864010197608688708669008257074873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94222398263647077137/20000000000000000000)
  centralHi := (235555995659117692843/50000000000000000000)
  directionLo := (236875647416891058639/50000000000000000000)
  directionHi := (473751294833782117279/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree091.table
  base := (16107554526707761851896319240673888672071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2671260)
      previous := (1335630)
      next := (1335630)
      square := (17530076137475426955592006112505000000000000)
      linear := (-1674024288047283591578532140324186500000000000)
      constant := (40682100160503463546491115456575053697569272991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree091.table
  base := (8053777194187408254191516574926168960423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1335630)
      previous := (667815)
      next := (667815)
      square := (8765038068737713477796003056252500000000000)
      linear := (-837912187427224657362815422766605750000000000)
      constant := (20384047739709617025201511383231342468286992383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236875647416891058639/50000000000000000000)
  centralHi := (473751294833782117279/100000000000000000000)
  directionLo := (476375975831629452117/100000000000000000000)
  directionHi := (238187987915814726059/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree092.table
  base := (16822297263055321352048578026340529355121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-82928036633552185345070748441183203500000000000)
      constant := (2038231233682053842871651724842855705663547760009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree092.table
  base := (33644594290429239155325401628927426674781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (785350440)
      previous := (392675220)
      next := (392675220)
      square := (5153842384417775524944049797076470000000000000)
      linear := (-498103260987689139319685213487689421000000000000)
      constant := (12255228569651834435883677907153127652559224960447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476375975831629452117/100000000000000000000)
  centralHi := (238187987915814726059/50000000000000000000)
  directionLo := (478986274691028349411/100000000000000000000)
  directionHi := (119746568672757087353/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree093.table
  base := (17549783205379256844306394346308421250909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-83828883152787474702793422006481268500000000000)
      constant := (2083539739422759168889152530213859906903074259861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree093.table
  base := (17549783105006996566709910602636979843949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-83919025961361696685005826398102443500000000000)
      constant := (2087940708383329230112027223124393011001990218021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478986274691028349411/100000000000000000000)
  centralHi := (119746568672757087353/25000000000000000000)
  directionLo := (120395606319136840193/25000000000000000000)
  directionHi := (481582425276547360773/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree094.table
  base := (36580024648203934305420342825789961127773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-169459459344045528121032191143558667000000000000)
      constant := (4258696850044522594229554220529107671109109504917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree094.table
  base := (36580024477237100466080852401262616604837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-169641683516217073633461567763179967000000000000)
      constant := (4267689037504115179821982875584016102739333455773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120395606319136840193/25000000000000000000)
  centralHi := (481582425276547360773/100000000000000000000)
  directionLo := (484164655182607665287/100000000000000000000)
  directionHi := (60520581897825958161/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree095.table
  base := (38085969188633243814485721875386021672957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-171261152382516106836477538274154797000000000000)
      constant := (4351314580852450509596505087318753657474184211253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree095.table
  base := (1904298452152173248454283875691056561649/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3272293500000000000000000000000000000000000000
      center := (39267522)
      previous := (19633761)
      next := (19633761)
      square := (257692119220888776247202489853823500000000000)
      linear := (-25716797266456613084536722409523257050000000000)
      constant := (654074857798394978374700975666365088289632743963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484164655182607665287/100000000000000000000)
  centralHi := (60520581897825958161/12500000000000000000)
  directionLo := (243366592983170882861/50000000000000000000)
  directionHi := (486733185966341765723/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree096.table
  base := (3961739999010348924793459557222951571641/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (26178348)
      previous := (13089174)
      next := (13089174)
      square := (171794746147259184164801659902549000000000000)
      linear := (-17306284542098668555192288540475092700000000000)
      constant := (444493267117780231563410374095887359519130419089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree096.table
  base := (39617399866137719573191623577009378165767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-173248946703204434160361397697130127000000000000)
      constant := (4454311460132125447424927433711325083740587517743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243366592983170882861/50000000000000000000)
  centralHi := (486733185966341765723/100000000000000000000)
  directionLo := (97857646673890026471/20000000000000000000)
  directionHi := (122322058342362533089/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree097.table
  base := (41174317017303031161938484126872168740781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-174864538459457264267368232535347057000000000000)
      constant := (4539551120943544646858094481762872179400907234149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree097.table
  base := (41174316911760974962636072652184795841603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-175052578296698114423811312664105207000000000000)
      constant := (4549126261856764429552619355241620619487536350987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97857646673890026471/20000000000000000000)
  centralHi := (122322058342362533089/25000000000000000000)
  directionLo := (15369687735302641873/3125000000000000000)
  directionHi := (491830007529684539937/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree098.table
  base := (334036876878962323502820375561065970571/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1335630)
      previous := (667815)
      next := (667815)
      square := (8765038068737713477796003056252500000000000)
      linear := (-901358323969019607055171324826240750000000000)
      constant := (23648826173902205231281864805956117228425327712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree098.table
  base := (21378360075330131956440248930094555260441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667815000000000000000000000000000000000000000
      center := (8013780)
      previous := (4006890)
      next := (4006890)
      square := (52590228412426280866776018337515000000000000)
      linear := (-5413965608883422286344731458094294500000000000)
      constant := (142192146645900018547286794725382365084250281283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15369687735302641873/3125000000000000000)
  centralHi := (491830007529684539937/100000000000000000000)
  directionLo := (494358713182544814827/100000000000000000000)
  directionHi := (123589678295636203707/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree099.table
  base := (693197025542158774278998417312367221277/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-44616981134099605424564731699134829250000000000)
      constant := (1182947274636772017015996337340909669179843080528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree099.table
  base := (5545576194777541529389773685232564285171/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-44664960370921368737677785649513841750000000000)
      constant := (1185440761451583771386480484606750415964929612918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494358713182544814827/100000000000000000000)
  centralHi := (123589678295636203707/25000000000000000000)
  directionLo := (49687454985373688961/10000000000000000000)
  directionHi := (496874549853736889611/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree100.table
  base := (45997985178823609641855389276995511840893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-180269617574869000413704273927135447000000000000)
      constant := (4829408626284385810751216700302901691950751465397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree100.table
  base := (45997985113732206853973396318243317884731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-180463473077179155214161057565030447000000000000)
      constant := (4839585027932390643232127900297847227021759333699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49687454985373688961/10000000000000000000)
  centralHi := (496874549853736889611/100000000000000000000)
  directionLo := (124844428010726044111/25000000000000000000)
  directionHi := (99875542408580835289/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree101.table
  base := (47656846855171706689226853640310769366983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-182071310613339579129149621057731577000000000000)
      constant := (4928028513258086615364601220017853634386385057007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree101.table
  base := (744638231246515600742936355517973969803/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 16361467500000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1288460596104443881236012449269117500000000000)
      linear := (-136700328503004626608208229399004145250000000000)
      constant := (3703807052579675600049856454937568547845777701776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124844428010726044111/25000000000000000000)
  centralHi := (99875542408580835289/20000000000000000000)
  directionLo := (62733548674888883693/12500000000000000000)
  directionHi := (100373677879822213909/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree102.table
  base := (24670597324422351046964955117362476456957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-91936501825905078922297484094163853500000000000)
      constant := (2513824379717845303465510178478640745402668947253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree102.table
  base := (49341194601706788805604830059065820469747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-184070736264166515741060887498980607000000000000)
      constant := (5038236172295910697683704052400087484263546703163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62733548674888883693/12500000000000000000)
  centralHi := (100373677879822213909/20000000000000000000)
  directionLo := (504346766888526645779/100000000000000000000)
  directionHi := (25217338344426332289/5000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree103.table
  base := (51051028547315281669828410704941823089901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-185674696690280736560040315318923837000000000000)
      constant := (5128269364789869086261306705535804211383488638629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree103.table
  base := (12762757126801827871080568130039615145491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-46468591964415049001127700616488921750000000000)
      constant := (1284766333618639101680722509165892928088727835739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504346766888526645779/100000000000000000000)
  centralHi := (25217338344426332289/5000000000000000000)
  directionLo := (63351628119341018271/12500000000000000000)
  directionHi := (506813024954728146169/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree104.table
  base := (52786348540052768150696118865879587868929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-187476389728751315275485662449519967000000000000)
      constant := (5229890329297649075509547010954816499444116812441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree104.table
  base := (26393174252964771299350217967259981299027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32722935000000000000000000000000000000000000000
      center := (392675220)
      previous := (196337610)
      next := (196337610)
      square := (2576921192208887762472024898538235000000000000)
      linear := (-281516999176730814401941076149396150500000000000)
      constant := (7861345334929391847185820186457529931229855216849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63351628119341018271/12500000000000000000)
  centralHi := (506813024954728146169/100000000000000000000)
  directionLo := (254633669836008702103/50000000000000000000)
  directionHi := (509267339672017404207/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree105.table
  base := (54547154618208163203184233740443792641943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (5342520)
      previous := (2671260)
      next := (2671260)
      square := (35060152274950853911184012225010000000000000)
      linear := (-3862818015657589673284306317961553000000000000)
      constant := (108826768427341351595726310138113438092211944303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree105.table
  base := (54547154589179347589143890094576504164333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (5342520)
      previous := (2671260)
      next := (2671260)
      square := (35060152274950853911184012225010000000000000)
      linear := (-3866972062135664419008380253059303000000000000)
      constant := (109055731402286911535000299103247630541900269493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254633669836008702103/50000000000000000000)
  centralHi := (509267339672017404207/100000000000000000000)
  directionLo := (511709882892118870873/100000000000000000000)
  directionHi := (255854941446059435437/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree106.table
  base := (7041680846793596562275820938271353683233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-47769943951423118176594089177678056750000000000)
      constant := (1359033333924971476519349050184969725108459206514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree106.table
  base := (56333446749656039255371885561652917052981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-191285262638141236794860547366880927000000000000)
      constant := (5447567180736022047148952368883709938485672587949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511709882892118870873/100000000000000000000)
  centralHi := (255854941446059435437/50000000000000000000)
  directionLo := (257070411192302558581/50000000000000000000)
  directionHi := (514140822384605117163/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree107.table
  base := (11629045000446922395075463278499602416409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-38576293768832610284364340768261671400000000000)
      constant := (1108151075512903080596539728151597190959866309361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree107.table
  base := (58145224981232142590838282094933694735079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (785350440)
      previous := (392675220)
      next := (392675220)
      square := (5153842384417775524944049797076470000000000000)
      linear := (-579266682694904751174931387001568021000000000000)
      constant := (16657217748034352338506413004016026206425166467373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257070411192302558581/50000000000000000000)
  centralHi := (514140822384605117163/100000000000000000000)
  directionLo := (51656032197137453343/10000000000000000000)
  directionHi := (516560321971374533431/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree108.table
  base := (11996497859326004174709766595673057938523/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-38936632376526726027453410194380897400000000000)
      constant := (1129275555704438594624378170138212383611568141667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree108.table
  base := (59982489278767875371596770684010274525089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-194892525825128597321760377300831087000000000000)
      constant := (5658247044527132278299347185874862706174442881081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51656032197137453343/10000000000000000000)
  centralHi := (516560321971374533431/100000000000000000000)
  directionLo := (20758741666219450529/4000000000000000000)
  directionHi := (259484270827743131613/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree109.table
  base := (15461309913286235360090577499455836632233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-49121213730276052213178099525625154250000000000)
      constant := (1438250134640835394549131818520756911332478624257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree109.table
  base := (61845239637954875775496534581523074179993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-196696157418622277585210292267806167000000000000)
      constant := (5765090566273667727283066073384221248492805949297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20758741666219450529/4000000000000000000)
  centralHi := (259484270827743131613/50000000000000000000)
  directionLo := (260682818872319545701/50000000000000000000)
  directionHi := (521365637744639091403/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree110.table
  base := (63733476068101196852382030347733119612983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-198286547959574787568157745233096747000000000000)
      constant := (5860623657679937168799155014437589279696191191007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree110.table
  base := (63733476055184569625841477898990708359407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (785350440)
      previous := (392675220)
      next := (392675220)
      square := (5153842384417775524944049797076470000000000000)
      linear := (-595499367036347873545980621704343741000000000000)
      constant := (17618809443729554751714542019497744363049766379909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260682818872319545701/50000000000000000000)
  centralHi := (521365637744639091403/100000000000000000000)
  directionLo := (130937940742390986527/25000000000000000000)
  directionHi := (523751762969563946109/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree111.table
  base := (65647198538419833373396681448265572077167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-200088240998045366283603092363692877000000000000)
      constant := (5969247135865262918064570743233784962187930048343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree111.table
  base := (1025737476991207742559754439056838062367/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-50075855151402409528027530550439081750000000000)
      constant := (1495446197357274092313253064695696978601718706288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130937940742390986527/25000000000000000000)
  centralHi := (523751762969563946109/100000000000000000000)
  directionLo := (263063533298791887331/50000000000000000000)
  directionHi := (526127066597583774663/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree112.table
  base := (13517281412305242344678033279815240770757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89042000000000000000000000000000000000000000
      center := (1068504)
      previous := (534252)
      next := (534252)
      square := (7012030454990170782236802445002000000000000)
      linear := (-824040547087820183669585467323628600000000000)
      constant := (24811718257606947656077062141292665534354872397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree112.table
  base := (67586407052188917518698769288535624391871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (5342520)
      previous := (2671260)
      next := (2671260)
      square := (35060152274950853911184012225010000000000000)
      linear := (-4124633718349047313786939534055743000000000000)
      constant := (124319091649508073623491131804667790533550488791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263063533298791887331/50000000000000000000)
  centralHi := (526127066597583774663/100000000000000000000)
  directionLo := (528491694541579725751/100000000000000000000)
  directionHi := (66061461817697465719/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree113.table
  base := (69551101635270054202550942144272115831527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-203691627074986523714493786624885137000000000000)
      constant := (6189495169420564048661891282875164580577835264783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree113.table
  base := (8693887703416521257759763734581652391237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16361467500000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1288460596104443881236012449269117500000000000)
      linear := (-152933012844447748979257464101779865250000000000)
      constant := (4651866439071739178420875134919770039856417168238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528491694541579725751/100000000000000000000)
  centralHi := (66061461817697465719/12500000000000000000)
  directionLo := (530845789464588733607/100000000000000000000)
  directionHi := (66355723683073591701/12500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree114.table
  base := (71541282257858093631879582218349989278633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-205493320113457102429939133755481267000000000000)
      constant := (6301119724781936472477868478191306546761026969857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree114.table
  base := (14308256450222082793360909270309737735999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-41142863077218135780491973420536313400000000000)
      constant := (1262868814646906820190799068644857073453476162471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530845789464588733607/100000000000000000000)
  centralHi := (66355723683073591701/12500000000000000000)
  directionLo := (106637898176048935881/20000000000000000000)
  directionHi := (266594745440122339703/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree115.table
  base := (36778474463898670271521979893408845395317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-103647506575963840572692240443038698500000000000)
      constant := (3206872319597281223682475347122003082586400499693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree115.table
  base := (73556948922061847717328860638794255983837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-207517946979584359165909782069656647000000000000)
      constant := (6427201954239352234331136378265809324462163946773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106637898176048935881/20000000000000000000)
  centralHi := (266594745440122339703/50000000000000000000)
  directionLo := (66940366906157904133/12500000000000000000)
  directionHi := (107104587049852646613/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree116.table
  base := (75598101643847297152987924195150752788621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-209096706190398259860829828016673527000000000000)
      constant := (6527369912655735791434965229752049328580207581509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree116.table
  base := (1889952540974313163032082068010064351743/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3272293500000000000000000000000000000000000000
      center := (39267522)
      previous := (19633761)
      next := (19633761)
      square := (257692119220888776247202489853823500000000000)
      linear := (-31398236785961705914403954555494759050000000000)
      constant := (981159334266118757338546102408704300851161330282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66940366906157904133/12500000000000000000)
  centralHi := (107104587049852646613/20000000000000000000)
  directionLo := (537846256072159192089/100000000000000000000)
  directionHi := (53784625607215919209/10000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree117.table
  base := (19416185101244927415010266454006721289933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-52724599807217209644068793786817414250000000000)
      constant := (1660498886290803334800051959417888317188906247557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree117.table
  base := (38832370200418400509808812298369517202571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-105562605083285859846404806001803403500000000000)
      constant := (3327962447918329345745454429512144261493407511059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537846256072159192089/100000000000000000000)
  centralHi := (53784625607215919209/10000000000000000000)
  directionLo := (540159583978374575907/100000000000000000000)
  directionHi := (135039895994593643977/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree118.table
  base := (79756865210344672022476095038535421278381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-212700092267339417291720522277865787000000000000)
      constant := (6757621536715140995983375225624917650046005224549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree118.table
  base := (79756865206824006225807555941096117591941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-212928841760065399956259526970581887000000000000)
      constant := (6771789956425141042275553471351296948314229457789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540159583978374575907/100000000000000000000)
  centralHi := (135039895994593643977/25000000000000000000)
  directionLo := (542463046811985851297/100000000000000000000)
  directionHi := (271231523405992925649/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree119.table
  base := (81874476059242081136995934667432427206657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (5342520)
      previous := (2671260)
      next := (2671260)
      square := (35060152274950853911184012225010000000000000)
      linear := (-4377587455220612163411548355274733000000000000)
      constant := (140290773210407989113502751512152636091667576297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree119.table
  base := (40937238028125207740242992796489414362207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667815000000000000000000000000000000000000000
      center := (8013780)
      previous := (4006890)
      next := (4006890)
      square := (52590228412426280866776018337515000000000000)
      linear := (-6573443061843645312848248222578274500000000000)
      constant := (210877267659328995869655880266126238650459453541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542463046811985851297/100000000000000000000)
  centralHi := (271231523405992925649/50000000000000000000)
  directionLo := (108951353942829881713/20000000000000000000)
  directionHi := (272378384857074704283/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree120.table
  base := (21004393237774400177214560625377242504349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-54075869586070143680652804134764511750000000000)
      constant := (1747968649236627954913063416510844175463269969621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree120.table
  base := (672140583588445035278996959405305249529/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (52356696)
      previous := (26178348)
      next := (26178348)
      square := (343589492294518368329603319805098000000000000)
      linear := (-43307220989410552096631871380906409400000000000)
      constant := (1401305451434850926481009104786711091892493746025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108951353942829881713/20000000000000000000)
  centralHi := (272378384857074704283/50000000000000000000)
  directionLo := (109408175040487146867/20000000000000000000)
  directionHi := (8547513675038058349/1562500000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree121.table
  base := (86186155885442423719681900820171286121163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-218105171382751153438056563669654177000000000000)
      constant := (7110501665623679339149229810108721057640614598227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree121.table
  base := (538663474270516878962293913372887643893/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1090764500000000000000000000000000000000000000
      center := (13089174)
      previous := (6544587)
      next := (6544587)
      square := (85897373073629592082400829951274500000000000)
      linear := (-10916986827027322037330463593575356350000000000)
      constant := (356269974866633325015172786186647984771154019176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109408175040487146867/20000000000000000000)
  centralHi := (8547513675038058349/1562500000000000000)
  directionLo := (549315483247194594089/100000000000000000000)
  directionHi := (54931548324719459409/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree122.table
  base := (88380224861896235148668320838303052587469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-219906864421221732153501910800250307000000000000)
      constant := (7230129093340664356805555531697706209008088660101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree122.table
  base := (44190112430030702566646603723307279267189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32722935000000000000000000000000000000000000000
      center := (392675220)
      previous := (196337610)
      next := (196337610)
      square := (2576921192208887762472024898538235000000000000)
      linear := (-330215052201060181515088780257723310500000000000)
      constant := (10867911196018762721503528488201930602897414655943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549315483247194594089/100000000000000000000)
  centralHi := (54931548324719459409/10000000000000000000)
  directionLo := (275790355672542953947/50000000000000000000)
  directionHi := (110316142269017181579/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree123.table
  base := (22649944970038217692616404185999026874799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-55427139364923077717236814482711609250000000000)
      constant := (1837689220024199741621215789176741488849153387671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree123.table
  base := (90599779878594163994753707883326688748467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-221946999727533801273509101805457287000000000000)
      constant := (7366151157213131397473020386070606773978754466043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275790355672542953947/50000000000000000000)
  centralHi := (110316142269017181579/20000000000000000000)
  directionLo := (553836674589903841277/100000000000000000000)
  directionHi := (276918337294951920639/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree124.table
  base := (23211205234992061801069054093981129718157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5453822500000000000000000000000000000000000000
      center := (65445870)
      previous := (32722935)
      next := (32722935)
      square := (429486865368147960412004149756372500000000000)
      linear := (-55877562624540722396098151265360641750000000000)
      constant := (1868096256472887673303381184584243774432921322053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree124.table
  base := (46422410469322098725060794532982164638923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (130891740)
      previous := (65445870)
      next := (65445870)
      square := (858973730736295920824008299512745000000000000)
      linear := (-111875315660513740768479508386216183500000000000)
      constant := (3744015288467009353892229780437685812642585053267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553836674589903841277/100000000000000000000)
  centralHi := (276918337294951920639/50000000000000000000)
  directionLo := (2780417428704074537/500000000000000000)
  directionHi := (556083485740814907401/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree125.table
  base := (95115348041150205254978669649610415857011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-225311943536633468299837952192038697000000000000)
      constant := (7595013530724500336134766174706392710894129349819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree125.table
  base := (9511534804002555899768745130674406035367/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6544587000000000000000000000000000000000000000
      center := (78535044)
      previous := (39267522)
      next := (39267522)
      square := (515384238441777552494404979707647000000000000)
      linear := (-67666278874356348540122679521822234100000000000)
      constant := (2283273716952429429275222673467227343971784408429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2780417428704074537/500000000000000000)
  centralHi := (556083485740814907401/100000000000000000000)
  directionLo := (558321255288124557061/100000000000000000000)
  directionHi := (279160627644062278531/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree126.table
  base := (48705680591774982466114039190009753025537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2671260)
      previous := (1335630)
      next := (1335630)
      square := (17530076137475426955592006112505000000000000)
      linear := (-2317486087501061704237584686965661500000000000)
      constant := (78761657087707380891683983167576725714449932777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree126.table
  base := (48705680591297376448947990496650607640559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2671260)
      previous := (1335630)
      next := (1335630)
      square := (17530076137475426955592006112505000000000000)
      linear := (-2319978515387906551672029048024311500000000000)
      constant := (78926495876888331905659715044564255702765327239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558321255288124557061/100000000000000000000)
  centralHi := (279160627644062278531/50000000000000000000)
  directionLo := (560550091516680791721/100000000000000000000)
  directionHi := (280275045758340395861/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree127.table
  base := (99732860367054938012934611530958776958573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-228915329613574625730728646453230957000000000000)
      constant := (7843271617503774052490588329474799218739658798117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree127.table
  base := (99732860366243685091939526026688590206551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-229161526101508522327308761673357607000000000000)
      constant := (7859683195214658184972172450829225167504706996479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560550091516680791721/100000000000000000000)
  centralHi := (280275045758340395861/50000000000000000000)
  directionLo := (562770100567017746509/100000000000000000000)
  directionHi := (56277010056701774651/10000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree128.table
  base := (10207984559158268402101748042221436550517/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (26178348)
      previous := (13089174)
      next := (13089174)
      square := (171794746147259184164801659902549000000000000)
      linear := (-23071702265204520444617399358382708700000000000)
      constant := (796890119944967266516209606501447473856612800493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree128.table
  base := (12759980698861717123126005410884002353289/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16361467500000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1288460596104443881236012449269117500000000000)
      linear := (-173223868271251651943069007480249515250000000000)
      constant := (5989179140760048672619089511789530072618609193286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell119.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562770100567017746509/100000000000000000000)
  centralHi := (56277010056701774651/10000000000000000000)
  directionLo := (564981386494336931231/100000000000000000000)
  directionHi := (17655668327948029101/3125000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree129.table
  base := (104452316857075829211282166229977417960771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-232518715690515783161619340714423217000000000000)
      constant := (8095531140432894002910573103586360774626542798859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree129.table
  base := (104452316856490784723277103398831597247911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (261783480)
      previous := (130891740)
      next := (130891740)
      square := (1717947461472591841648016599025490000000000000)
      linear := (-232768789288495882854208591607307767000000000000)
      constant := (8112463573331158589557783015446375133512638035919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell119.Kernel129
