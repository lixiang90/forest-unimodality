import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell013.Parameters
import ForestUnimodality.BinomialMassData.Q89_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q89_255.Batch050_099
import ForestUnimodality.BinomialMassData.Q89_255.Batch100_149
import ForestUnimodality.BinomialMassData.Q91_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q91_255.Batch050_099
import ForestUnimodality.BinomialMassData.Q91_255.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree000.table
  base := (919762671795884866442705173/100000000000000000000000000)
  polynomial :=
    { denominator := 1275000000000000000000000000000000000000000
      center := (2158)
      previous := (1157)
      next := (0)
      square := (31661097500734487926454808075000000000000)
      linear := (71377587101749924436422390050000000000000)
      constant := (11726974065397532047144490955750000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree000.table
  base := (919762671795884866442705173/100000000000000000000000000)
  polynomial :=
    { denominator := 1275000000000000000000000000000000000000000
      center := (2132)
      previous := (1183)
      next := (0)
      square := (31661097500734487926454808075000000000000)
      linear := (71377587101749924436422390050000000000000)
      constant := (11726974065397532047144490955750000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree001.table
  base := (30924705227114065172170516982765109573241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (2513121871163098376075750725080000000000000)
      constant := (401101966548445165284689998766803249999999205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree001.table
  base := (30588460424481986251447215021706286043829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (2487792993162510785734586878620000000000000)
      constant := (396709491459374486335735180929493249999996145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (47666017369207587121/100000000000000000000)
  directionHi := (23833008684603793561/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree002.table
  base := (41767016957717468816709499628136347558631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (2771973600273901211787919115220000000000000)
      constant := (539671540295374258346079720083017199999996155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree002.table
  base := (4087880244488525409130260898608402921953/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (1335329044135775425211631864690000000000000)
      constant := (264038811624315082520837588218643399999993825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47666017369207587121/100000000000000000000)
  centralHi := (23833008684603793561/50000000000000000000)
  directionLo := (67409928227844885977/100000000000000000000)
  directionHi := (33704964113922442989/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree003.table
  base := (14152410839777016167706621772979807451737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (86283909703600945237389463380000000000000)
      constant := (60670268300735905558782118689476465303279895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree003.table
  base := (13710166568279731318833409245320407344267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (60955031703013354896225616920000000000000)
      constant := (58751407160955097923621052792892965837397445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67409928227844885977/100000000000000000000)
  centralHi := (33704964113922442989/50000000000000000000)
  directionLo := (41279981938964066589/50000000000000000000)
  directionHi := (82559963877928133179/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree004.table
  base := (19208802847273051924163615336608439363797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-1736566683830689868939245554660000000000000)
      constant := (245940588473109535052585075472128753926179985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree004.table
  base := (18420451037220270344486272073300004727653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-1939197707835390591668556326340000000000000)
      constant := (235745732232654147165126054597602561483127265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41279981938964066589/50000000000000000000)
  centralHi := (82559963877928133179/100000000000000000000)
  directionLo := (95332034738415174243/100000000000000000000)
  directionHi := (23833008684603793561/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree005.table
  base := (12987221764544727897688265385608592260959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-3990836825882985409302827889600000000000000)
      constant := (166028414555687518538789903352589742353771795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree005.table
  base := (12322520577398446525587474366438049348093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-4244125605888861312714466354200000000000000)
      constant := (157545445468453498838188082702076831771949465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95332034738415174243/100000000000000000000)
  centralHi := (23833008684603793561/25000000000000000000)
  directionLo := (53292227527116927889/50000000000000000000)
  directionHi := (106584455054233855779/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree006.table
  base := (1734125901193862410216857155017389763581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-2081702322645093649888803408180000000000000)
      constant := (37225801592441886135514959435433923125618175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree006.table
  base := (8126387902700390624433992159608033881437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-2183017834647444011253458794020000000000000)
      constant := (34966860598913289107718695722972826876029395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53292227527116927889/50000000000000000000)
  centralHi := (106584455054233855779/100000000000000000000)
  directionLo := (58378710312599396077/50000000000000000000)
  directionHi := (23351484125039758431/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree007.table
  base := (11243453052062314374493777190576996759/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-4249688554993788245014996279740000000000000)
      constant := (37299739274296481428751116783450460712698750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree007.table
  base := (5182241297610027409129017429618887452859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-8853981401995802754806286409920000000000000)
      constant := (69360339857226694229212079656527631324431295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58378710312599396077/50000000000000000000)
  centralHi := (23351484125039758431/20000000000000000000)
  directionLo := (63056213973904260433/50000000000000000000)
  directionHi := (126112427947808520867/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree008.table
  base := (3421242290577429232408607363491457821911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-10753647252039872030393574894420000000000000)
      constant := (49342022572831824762316067526590408973952555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree008.table
  base := (1533751357905296713593836621216036108471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-5579454650024636737926098218890000000000000)
      constant := (22714546078782235428395117818866549590665355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63056213973904260433/50000000000000000000)
  centralHi := (126112427947808520867/100000000000000000000)
  directionLo := (67409928227844885977/50000000000000000000)
  directionHi := (26963971291137954391/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree009.table
  base := (1792908437954058018535804083926276208557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-4335972464697389190252385743120000000000000)
      constant := (10770722268910353861902972683462407364094595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree009.table
  base := (753438431170811487334488779269154625159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-2243972866350457366149684410940000000000000)
      constant := (4921103897798723454356347281452785300064265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67409928227844885977/50000000000000000000)
  centralHi := (26963971291137954391/20000000000000000000)
  directionLo := (35749513026905690341/25000000000000000000)
  directionHi := (28599610421524552273/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree010.table
  base := (554268368238093308215618494057240738673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-15262187536144463111120739564300000000000000)
      constant := (21137063168292705490126537424014415806442365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree010.table
  base := (80139339079107098151654936237321697251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-7884382548078107458972008246750000000000000)
      constant := (9657275780739465416199377013732737345498510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35749513026905690341/25000000000000000000)
  centralHi := (28599610421524552273/20000000000000000000)
  directionLo := (7536659093792154841/5000000000000000000)
  directionHi := (150733181875843096821/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree011.table
  base := (-207777882480114328763578502530171420877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-8758228839098379325742160949620000000000000)
      constant := (7122347632608939395048175411598120671494615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree011.table
  base := (-609310149785423329116419696803716958189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-18073692994209685638989926521360000000000000)
      constant := (13260180892121009879000408076393660958752055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7536659093792154841/5000000000000000000)
  centralHi := (150733181875843096821/100000000000000000000)
  directionLo := (39522573716056240371/25000000000000000000)
  directionHi := (31618058972844992297/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree012.table
  base := (-299245877334767554525016551668153777581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-3295121303374842365307984039030000000000000)
      constant := (1764867813281996710270541869461106748372730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree012.table
  base := (-680171750448769024423898155606106773359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-3396436815377192726672639424870000000000000)
      constant := (1725681884226172279688630913231527137488735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39522573716056240371/25000000000000000000)
  centralHi := (31618058972844992297/20000000000000000000)
  directionLo := (165119927755856266357/100000000000000000000)
  directionHi := (82559963877928133179/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree013.table
  base := (-1843817623699088459909453843070900169513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-22024997962301349732211486569120000000000000)
      constant := (9470893133512464495992725361276943295483435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree013.table
  base := (-991994168238659626080798621871321360493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-11341774395158313540540873288540000000000000)
      constant := (4963616130021734949950941454830465706788535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165119927755856266357/100000000000000000000)
  centralHi := (82559963877928133179/50000000000000000000)
  directionLo := (171862269721835083191/100000000000000000000)
  directionHi := (21482783715229385399/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree014.table
  base := (-239231837078799849751168065630315822633/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-12139634052176822636287534452030000000000000)
      constant := (5209094654822648214199650903196713633289175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree014.table
  base := (-2514630707361736679786015990912082413719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-24988476688370097802127656604940000000000000)
      constant := (11532413165045527066140543945004368209584405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171862269721835083191/100000000000000000000)
  centralHi := (21482783715229385399/12500000000000000000)
  directionLo := (11146869124224410053/6250000000000000000)
  directionHi := (178349905987590560849/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree015.table
  base := (-2867155584863452421672789305754660046017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-8844512748801980270979550413000000000000000)
      constant := (4370088071189903539476865255603548700516305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree015.table
  base := (-2975504977199801336532054179724587780661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-9097801528807856174391188877600000000000000)
      constant := (4955823707035939019760230808743911970834565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11146869124224410053/6250000000000000000)
  centralHi := (178349905987590560849/100000000000000000000)
  directionLo := (18460969145097445499/10000000000000000000)
  directionHi := (184609691450974454991/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree016.table
  base := (-3285315680510816223424580105292798718991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-28787808388458236353302233573940000000000000)
      constant := (17326209523603022352718044160683152659522045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree016.table
  base := (-1691263684248800597634422597521162860007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-14799166242238519622109738330330000000000000)
      constant := (9862707827269332896079624341605277005608965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18460969145097445499/10000000000000000000)
  centralHi := (184609691450974454991/100000000000000000000)
  directionLo := (95332034738415174243/50000000000000000000)
  directionHi := (190664069476830348487/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree017.table
  base := (-3658668903471814272103664969262030562321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (12948)
      previous := (6942)
      next := (0)
      square := (189966585004406927558728848450000000000000)
      linear := (-1826004619441795993745047994640000000000000)
      constant := (1347744276110241541649353473056546619824435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree017.table
  base := (-1873393256405748297160000565905295248659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3825000000000000000000000000000000000000000
      center := (6396)
      previous := (3549)
      next := (0)
      square := (94983292502203463779364424225000000000000)
      linear := (-938331187721485587213687843780000000000000)
      constant := (763589385645517854849342277093449134775865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95332034738415174243/50000000000000000000)
  centralHi := (190664069476830348487/100000000000000000000)
  directionLo := (196532024365768922749/100000000000000000000)
  directionHi := (786128097463075691/400000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree018.table
  base := (-998914658419195955532429262718430693939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-5549391445427137905671566373970000000000000)
      constant := (4959464594731487698444273508855205883548870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree018.table
  base := (-2038082106195006327576771144737977734153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-5701364713430663447718549452730000000000000)
      constant := (5579139775848761945457375774304866522446745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196532024365768922749/100000000000000000000)
  centralHi := (786128097463075691/400000000000000000)
  directionLo := (202229784683534657931/100000000000000000000)
  directionHi := (50557446170883664483/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree019.table
  base := (-2151207566200251482702685480608702513247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-17775309407307561487196490289380000000000000)
      constant := (18890945049634496607702088538486823815222765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree019.table
  base := (-4376392609108682706440131322041050716107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-36513116178637451407357206744240000000000000)
      constant := (42189267778882248676397132541862135437028465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202229784683534657931/100000000000000000000)
  centralHi := (50557446170883664483/25000000000000000000)
  directionLo := (12985709547089396699/6250000000000000000)
  directionHi := (41554270550686069437/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree020.table
  base := (-4583491756075906806027977552587004944711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-37804888956667418514756562913700000000000000)
      constant := (46927743886103986253468569279406000694033445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree020.table
  base := (-2325872956085938546470991812364287423351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-19409022038345461064201558386050000000000000)
      constant := (26024870196306900871101829947202442059320245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12985709547089396699/6250000000000000000)
  centralHi := (41554270550686069437/20000000000000000000)
  directionLo := (53292227527116927889/25000000000000000000)
  directionHi := (213168910108467711557/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree021.table
  base := (-4842353331114110707048868436199256215009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-13353053032906571351706715082880000000000000)
      constant := (19049762953805783336125416685518224307935985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree021.table
  base := (-613186867434181469273466600793923971377/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-6853828662457398808241504466660000000000000)
      constant := (10502286584929605729432326103474358336322820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53292227527116927889/25000000000000000000)
  centralHi := (213168910108467711557/100000000000000000000)
  directionLo := (10921656633573679957/5000000000000000000)
  directionHi := (218433132671473599141/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree022.table
  base := (-5081701650952661012833306820483080058499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-42313429240772009595483727583580000000000000)
      constant := (68411388201553794271656971382801543839220505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree022.table
  base := (-1028041501740258418442238946347433185247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-43427899872797863570494936827820000000000000)
      constant := (75047810660742796926118247399102157129313825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10921656633573679957/5000000000000000000)
  centralHi := (218433132671473599141/100000000000000000000)
  directionLo := (223573439076548595427/100000000000000000000)
  directionHi := (55893359769137148857/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree023.table
  base := (-5303693769700785589577042054755392687507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-44567699382824305135847309918520000000000000)
      constant := (80685989417822810643435012970280118098971465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree023.table
  base := (-5357948458973053229412643099384066572007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-45732827770851334291540846855680000000000000)
      constant := (88125160613384184523960972780204214231048965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223573439076548595427/100000000000000000000)
  centralHi := (55893359769137148857/25000000000000000000)
  directionLo := (4571963773800347419/2000000000000000000)
  directionHi := (228598188690017370951/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree024.table
  base := (-5510089591363975333806801165295258107319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-15607323174958866892070297417820000000000000)
      constant := (31316734986210996671460096614077056104772135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree024.table
  base := (-5560414154753650694750927578903550853161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-16012585222968268337528918961180000000000000)
      constant := (34074569382545190238670764270285107051547065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4571963773800347419/2000000000000000000)
  centralHi := (228598188690017370951/100000000000000000000)
  directionLo := (233514841250397584309/100000000000000000000)
  directionHi := (23351484125039758431/10000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree025.table
  base := (-1140470539467800301995940623627284827099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-49076239666928896216574474588400000000000000)
      constant := (108185000947919322090227969845385804117887525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree025.table
  base := (-5749024074463134263565799577128163051127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-50342683566958275733632666911400000000000000)
      constant := (117324992946644208173978740445198239520093365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233514841250397584309/100000000000000000000)
  centralHi := (23351484125039758431/10000000000000000000)
  directionLo := (29791260855754741951/12500000000000000000)
  directionHi := (238330086846037935609/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree026.table
  base := (-1176344026306059116197990749008704856763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-51330509808981191756938056923340000000000000)
      constant := (123374289629704675696038906137644966688985925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree026.table
  base := (-2962492078880938602274445598102473839893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-26323805732505873227339288469630000000000000)
      constant := (66706665882563471269262820097405327712191535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29791260855754741951/12500000000000000000)
  centralHi := (238330086846037935609/100000000000000000000)
  directionLo := (48609990540168420817/20000000000000000000)
  directionHi := (121524976350421052043/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree027.table
  base := (-6049251475564619230366685712617414869651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-17861593317011162432433879752760000000000000)
      constant := (46501430381644338379172242796621506540062915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree027.table
  base := (-6089331452267868657002168675964242363853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-18317513121021739058574828989040000000000000)
      constant := (50158412599603941684343640370233009352697245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48609990540168420817/20000000000000000000)
  centralHi := (121524976350421052043/50000000000000000000)
  directionLo := (15479993227111524971/6250000000000000000)
  directionHi := (247679891633784399537/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree028.table
  base := (-310293200830742277557008130781151184041/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-27919525046542891418832610796610000000000000)
      constant := (78281538086960562919901429276063288515467950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree028.table
  base := (-6242966275543667971145827340049656609769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-57257467261118687896770396994980000000000000)
      constant := (168499002417797771367880943008878215789954155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15479993227111524971/6250000000000000000)
  centralHi := (247679891633784399537/100000000000000000000)
  directionLo := (252224855895617041733/100000000000000000000)
  directionHi := (126112427947808520867/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree029.table
  base := (-6352358496103359383679826572164410603283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-58093320235138078378028803928160000000000000)
      constant := (174540231074470892953892701878487840104304585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree029.table
  base := (-798334494157716469732994839455516374801/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-29781197579586079308908153511420000000000000)
      constant := (93737193225857241629264047789167038182851980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252224855895617041733/100000000000000000000)
  centralHi := (126112427947808520867/50000000000000000000)
  directionLo := (128344679616459347567/50000000000000000000)
  directionHi := (51337871846583739027/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree030.table
  base := (-6489438409349450841349941530670450352913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-20115863459063457972797462087700000000000000)
      constant := (64475535629984982851828001906543597720122145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree030.table
  base := (-1630288199158618367753159962853432742591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-10311220509537604889810369508450000000000000)
      constant := (34565397732207420626262349466860738121736030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128344679616459347567/50000000000000000000)
  centralHi := (51337871846583739027/20000000000000000000)
  directionLo := (65269382348870123551/25000000000000000000)
  directionHi := (52215505879096098841/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree031.table
  base := (-3308862414668895364428845466737393319201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-31300930259621334729377984299020000000000000)
      constant := (106607063283103824414679924704003199883790995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree031.table
  base := (-3323504037207035798042841204769383481401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-32086125477639550029954063539280000000000000)
      constant := (114122526346132905830585963005357167824379995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65269382348870123551/25000000000000000000)
  centralHi := (52215505879096098841/20000000000000000000)
  directionLo := (33174144103288854889/12500000000000000000)
  directionHi := (265393152826310839113/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree032.table
  base := (-6737768072392920891003423679012333734769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-64856130661294964999119550932980000000000000)
      constant := (233895633239428327083891695519468599779329155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree032.table
  base := (-3382391572136312074648548368652146014579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-33238589426666285390477018553210000000000000)
      constant := (125012672496126356134229189320270841080400105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33174144103288854889/12500000000000000000)
  centralHi := (265393152826310839113/100000000000000000000)
  directionLo := (269639712911379543909/100000000000000000000)
  directionHi := (26963971291137954391/10000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree033.table
  base := (-214064284122886015644740068909439317367/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-11185066800557876756580522211320000000000000)
      constant := (42577461345070375086039378275030288947424880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree033.table
  base := (-6874958523409789593254202843364256747991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-22927368917128680500666649044760000000000000)
      constant := (90909004722341222424408419326033946997459015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269639712911379543909/100000000000000000000)
  centralHi := (26963971291137954391/10000000000000000000)
  directionLo := (68455105722095694761/25000000000000000000)
  directionHi := (54764084577676555809/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree034.table
  base := (-217344600049179006454884224834552716957/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3825000000000000000000000000000000000000000
      center := (6474)
      previous := (3471)
      next := (0)
      square := (94983292502203463779364424225000000000000)
      linear := (-2040137380747045767054315164790000000000000)
      constant := (8173996170752705190546168522889074744446320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree034.table
  base := (-3488980713249196120002497121501940957471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3825000000000000000000000000000000000000000
      center := (6396)
      previous := (3549)
      next := (0)
      square := (94983292502203463779364424225000000000000)
      linear := (-2090795136748220947736642857710000000000000)
      constant := (8716014832051723426390835539915015167534685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68455105722095694761/25000000000000000000)
  centralHi := (54764084577676555809/20000000000000000000)
  directionLo := (69484563574677496083/25000000000000000000)
  directionHi := (277938254298709984333/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree035.table
  base := (-881633317528913275628646585645053774653/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-35809470543725925810105148968900000000000000)
      constant := (150621945349178788564317992934019302642550940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree035.table
  base := (-1768543033445229065007379687706338792573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-36695981273746491472045883595000000000000000)
      constant := (160436434907951996651777403974333128005176270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69484563574677496083/25000000000000000000)
  centralHi := (277938254298709984333/100000000000000000000)
  directionLo := (56399192339768830583/20000000000000000000)
  directionHi := (70498990424711038229/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree036.table
  base := (-714452156640988336259517753156904851707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-12312201871584024526762313378790000000000000)
      constant := (54240720842644028202836516081500087339250775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree036.table
  base := (-3581964721493770713597001675915709751379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-12616148407591075610856279536310000000000000)
      constant := (57717950780163144955482362468801398227772035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56399192339768830583/20000000000000000000)
  centralHi := (70498990424711038229/25000000000000000000)
  directionLo := (285996104215245522729/100000000000000000000)
  directionHi := (28599610421524552273/10000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree037.table
  base := (-722970178504472127636148686915305495951/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-38063740685778221350468731303840000000000000)
      constant := (175256573883214337836670111498779260125786225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree037.table
  base := (-7247535386150656975990411406250248608189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-78001818343599924386183587245720000000000000)
      constant := (372645080958402003790738525449769516850502055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285996104215245522729/100000000000000000000)
  centralHi := (28599610421524552273/10000000000000000000)
  directionLo := (28994106442196003161/10000000000000000000)
  directionHi := (289941064421960031611/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree038.table
  base := (-7308883853759745134390715571861024488531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-78381751513608738241301044942620000000000000)
      constant := (376446760897651949426845058958011376526654345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree038.table
  base := (-1465051868727675643316243867454414878811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-80306746241653395107229497273580000000000000)
      constant := (399881495356486055868424853975960672505314725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28994106442196003161/10000000000000000000)
  centralHi := (289941064421960031611/100000000000000000000)
  directionLo := (58766612987301140401/20000000000000000000)
  directionHi := (146916532468252851003/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree039.table
  base := (-3691157588511628631360641578809546274537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-13439336942610172296944104546260000000000000)
      constant := (67206991159070619787900659756621616899882105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree039.table
  base := (-7397341654584809649941454803028637813967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-27537224713235621942758469100480000000000000)
      constant := (142671274088263998976924308565792855076453055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58766612987301140401/20000000000000000000)
  centralHi := (146916532468252851003/50000000000000000000)
  directionLo := (14883709153116233211/5000000000000000000)
  directionHi := (297674183062324664221/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree040.table
  base := (-7450217070268556187757288130251755357097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-82890291797713329322028209612500000000000000)
      constant := (430895827729533936239131620700475921580953515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree040.table
  base := (-1492799360002575814745488710414038702827/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-84916602037760336549321317329300000000000000)
      constant := (457039272357616650969262224254127133348674325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14883709153116233211/5000000000000000000)
  centralHi := (297674183062324664221/100000000000000000000)
  directionLo := (301466363751686193641/100000000000000000000)
  directionHi := (150733181875843096821/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree041.table
  base := (-7512787557608263179256085150214922947229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-85144561939765624862391791947440000000000000)
      constant := (459405827919397962348833648081020927071286855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree041.table
  base := (-7525416218852933085475741799508753011947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-87221529935813807270367227357160000000000000)
      constant := (486955355971670860482929836068674667079629265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301466363751686193641/100000000000000000000)
  centralHi := (150733181875843096821/50000000000000000000)
  directionLo := (305211431118668251591/100000000000000000000)
  directionHi := (38151428889833531449/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree042.table
  base := (-118284435213589067978592483945934947849/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-14566472013636320067125895713730000000000000)
      constant := (81461607141297912161930632940363904034386720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree042.table
  base := (-1516354161099003085187143822979122242583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-29842152611289092663804379128340000000000000)
      constant := (172586616875137368874443403296335525392013475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305211431118668251591/100000000000000000000)
  centralHi := (38151428889833531449/12500000000000000000)
  directionLo := (154455549347819787361/50000000000000000000)
  directionHi := (308911098695639574723/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree043.table
  base := (-15245249141154311163843712783893292191/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-44826551111935107971559478308660000000000000)
      constant := (259492604882013052113710992859313933764011250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree043.table
  base := (-1908303282249490899776463793348226262327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-45915692865960374356229523706440000000000000)
      constant := (274725386079115103825481558769819634916874730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154455549347819787361/50000000000000000000)
  centralHi := (308911098695639574723/100000000000000000000)
  directionLo := (78141744649222532871/25000000000000000000)
  directionHi := (62513395719378026297/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree044.table
  base := (-7670191684057557542009795820134553874657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-91907372365922511483482538952260000000000000)
      constant := (550050682273785148777591143466206126860085715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree044.table
  base := (-1919969851911578930034255138164060179989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-47068156814987109716752478720370000000000000)
      constant := (291013174525667372689145743579080794718486110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78141744649222532871/25000000000000000000)
  centralHi := (62513395719378026297/20000000000000000000)
  directionLo := (316180589728449922969/100000000000000000000)
  directionHi := (31618058972844992297/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree045.table
  base := (-7713032287288003127668148422552323382661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-31387214169324935674615373762400000000000000)
      constant := (193988135843432153826513351226085678136164565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree045.table
  base := (-3860945633779564470521608363778227455301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-16073540254671281692425144578100000000000000)
      constant := (102580833259507896923895538260646383981270165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316180589728449922969/100000000000000000000)
  centralHi := (31618058972844992297/10000000000000000000)
  directionLo := (159876682581350783667/50000000000000000000)
  directionHi := (63950673032540313467/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree046.table
  base := (-7751260156929850823576373464541807620737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-96415912650027102564209703622140000000000000)
      constant := (614724905868079075240012348609009791892315315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree046.table
  base := (-7759357310090635942985935236919732713911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-98746169426081160875596777496460000000000000)
      constant := (649825311314756320127703147294354876055587445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159876682581350783667/50000000000000000000)
  centralHi := (63950673032540313467/20000000000000000000)
  directionLo := (161643329389673216189/50000000000000000000)
  directionHi := (323286658779346432379/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree047.table
  base := (-1556995430493000124487175973459376154729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-98670182792079398104573285957080000000000000)
      constant := (648330852604570880653926205238338065538746775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree047.table
  base := (-1558474901907732839979737332298517454873/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-101051097324134631596642687524320000000000000)
      constant := (685046023173718314832775935246982902496883175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161643329389673216189/50000000000000000000)
  centralHi := (323286658779346432379/100000000000000000000)
  directionLo := (32678175126000406923/10000000000000000000)
  directionHi := (326781751260004069231/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree048.table
  base := (-3907137233618003342418117117601533704841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-16820742155688615607489478048670000000000000)
      constant := (113796843628391993477135718312701351389514265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree048.table
  base := (-3910514730000929600203651298911325683513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-17226004203698017052948099592030000000000000)
      constant := (120191001496280080179835442251443403161971145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32678175126000406923/10000000000000000000)
  centralHi := (326781751260004069231/100000000000000000000)
  directionLo := (66047971102342506543/20000000000000000000)
  directionHi := (82559963877928133179/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree049.table
  base := (-7839233747336141125926063141323160700997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-103178723076183989185300450626960000000000000)
      constant := (718074471557979312009168773939938295083534015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree049.table
  base := (-3922699743984980561658617511561695087627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-52830476560120786519367253790020000000000000)
      constant := (379062131547821873920524199557863155385410865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66047971102342506543/20000000000000000000)
  centralHi := (82559963877928133179/25000000000000000000)
  directionLo := (333662121584453109851/100000000000000000000)
  directionHi := (83415530396113277463/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree050.table
  base := (-7859928092590106440910341355835118631483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-105432993218236284725664032961900000000000000)
      constant := (754210131304232678142848900543364282197563585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree050.table
  base := (-1966388411325314437019194229005792498563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-53982940509147521879890208803950000000000000)
      constant := (397989943754095541273579060940559337112376370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333662121584453109851/100000000000000000000)
  centralHi := (83415530396113277463/25000000000000000000)
  directionLo := (168524820569612214943/50000000000000000000)
  directionHi := (337049641139224429887/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree051.table
  base := (-7876422952234665937416846911097058535449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (4316)
      previous := (2314)
      next := (0)
      square := (63322195001468975852909616150000000000000)
      linear := (-2111514967848795691490737554840000000000000)
      constant := (15513474310623293185257949732856250073460505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree051.table
  base := (-19703883988931896789927487560966238651/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1275000000000000000000000000000000000000000
      center := (2132)
      previous := (1183)
      next := (0)
      square := (31661097500734487926454808075000000000000)
      linear := (-1081086361924985436086532623880000000000000)
      constant := (8183451767455916419729701262243721828799000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168524820569612214943/50000000000000000000)
  centralHi := (337049641139224429887/100000000000000000000)
  directionLo := (340403451515876331937/100000000000000000000)
  directionHi := (170201725757938165969/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree052.table
  base := (-7888776926496538306157149747124187997379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-109941533502340875806391197631780000000000000)
      constant := (829004885074696658352384414366953935094086105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree052.table
  base := (-7893454405334137992499766050242680046333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-112575736814401985201872237663620000000000000)
      constant := (874320125272102414715536723209057945997439335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340403451515876331937/100000000000000000000)
  centralHi := (170201725757938165969/50000000000000000000)
  directionLo := (171862269721835083191/50000000000000000000)
  directionHi := (343724539443670166383/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree053.table
  base := (-7897042484032632626769601655298849635139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-112195803644393171346754779966720000000000000)
      constant := (867662534648075693274839069470292460495017305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree053.table
  base := (-7901305250520581206781745255398176918839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-114880664712455455922918147691480000000000000)
      constant := (914803382949950813149791593581920709170498805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171862269721835083191/50000000000000000000)
  centralHi := (343724539443670166383/100000000000000000000)
  directionLo := (8675346110804627697/2500000000000000000)
  directionHi := (347013844432185107881/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree054.table
  base := (-7901266604115245223934400094451665801133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-38150024595481822295706120767220000000000000)
      constant := (302386509198829614504351144577864028752088445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree054.table
  base := (-988143755894389439996537638038345159511/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-19530932101751487773994009619890000000000000)
      constant := (159360213697694866980728095497871094934079260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8675346110804627697/2500000000000000000)
  centralHi := (347013844432185107881/100000000000000000000)
  directionLo := (21892016367224773529/6250000000000000000)
  directionHi := (70054452375119275293/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree055.table
  base := (-7901491351489304656466352367709596451133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-116704343928497762427481944636600000000000000)
      constant := (947495316867928313159640938179686698153015335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree055.table
  base := (-3952514007238174030943985412951961352669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-59745260254281198682504983873600000000000000)
      constant := (499196656467279747598001797381334742608539655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21892016367224773529/6250000000000000000)
  centralHi := (70054452375119275293/20000000000000000000)
  directionLo := (14140025835975715991/4000000000000000000)
  directionHi := (5523447592178014059/1562500000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree056.table
  base := (-493609649436383427547939171728589286403/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-59479307035275028983922763485770000000000000)
      constant := (494334706315657377340899593711805570642631880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree056.table
  base := (-1975243544436376232607019955059339532013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-60897724203307934043027938887530000000000000)
      constant := (520749509845799723840757966040314578772341870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14140025835975715991/4000000000000000000)
  centralHi := (5523447592178014059/1562500000000000000)
  directionLo := (356699811975181121697/100000000000000000000)
  directionHi := (178349905987590560849/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree057.table
  base := (-7890089448194025345455697089681684104181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-40404294737534117836069703102160000000000000)
      constant := (343560458761738800746544841658687899408375365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree057.table
  base := (-1578603963440601462287389286679855069261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-41366792101556446269033929267640000000000000)
      constant := (361825998552587460606333408283392141373767825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356699811975181121697/100000000000000000000)
  centralHi := (178349905987590560849/50000000000000000000)
  directionLo := (71974107865251421937/20000000000000000000)
  directionHi := (179935269663128554843/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree058.table
  base := (-1969631680482063124142557184268453001007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-61733577177327324524286345820710000000000000)
      constant := (536765407547098323606512256023769537443807930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree058.table
  base := (-7881192868947604542223683658260258697943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-126405304202722809528147697830780000000000000)
      constant := (1130329877524084062476751458599029335633251285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71974107865251421937/20000000000000000000)
  centralHi := (179935269663128554843/50000000000000000000)
  directionLo := (5672087080375829133/1562500000000000000)
  directionHi := (363013573144053064513/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree059.table
  base := (-3931546626711064486592847835304884216927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-62860712248353472294468136988180000000000000)
      constant := (558608688693482119105298905759022980758864365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree059.table
  base := (-491594892680634019625155755073220372357/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-64355116050388140124596803929320000000000000)
      constant := (588027170408486957715264477350845152459977720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5672087080375829133/1562500000000000000)
  centralHi := (363013573144053064513/100000000000000000000)
  directionLo := (91532406658330019743/25000000000000000000)
  directionHi := (366129626633320078973/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree060.table
  base := (-980476657113464420309723519769768679633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-21329282439793206688216642718550000000000000)
      constant := (193623458042905204549355761908992211095163780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree060.table
  base := (-7846018342380646683088310417887110206197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-43671719999609916990079839295500000000000000)
      constant := (407550365247154976615985645053259377256136005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91532406658330019743/25000000000000000000)
  centralHi := (366129626633320078973/100000000000000000000)
  directionLo := (369219382901948909981/100000000000000000000)
  directionHi := (184609691450974454991/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree061.table
  base := (-488794275972170658571982763220536572439/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-65114982390405767834831719323120000000000000)
      constant := (603550322857987710265051715805838375003446440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree061.table
  base := (-3911356474806927605364779025037336438643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-66660043948441610845642713957180000000000000)
      constant := (635059941734757232857499852957352439615447785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369219382901948909981/100000000000000000000)
  centralHi := (184609691450974454991/50000000000000000000)
  directionLo := (186141748354807258211/50000000000000000000)
  directionHi := (372283496709614516423/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree062.table
  base := (-7793798146422630906246100429494393242389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-132484234922863831210027020981180000000000000)
      constant := (1253296817243738587312957443224169415882731055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree062.table
  base := (-7795619880478208019197819897929661799829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-135625015794936692412331337942220000000000000)
      constant := (1318460472825693385251515305079328748293223855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186141748354807258211/50000000000000000000)
  centralHi := (372283496709614516423/100000000000000000000)
  directionLo := (75064519217584858081/20000000000000000000)
  directionHi := (187661298043962145203/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree063.table
  base := (-7763099837668262447699337763857807905897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-44912835021638708916796867772040000000000000)
      constant := (433443012235913648567202480604414402727936505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree063.table
  base := (-7764755012120345786273689802856142546067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-45976647897663387711125749323360000000000000)
      constant := (455890885775903208814322369915396622062799555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75064519217584858081/20000000000000000000)
  centralHi := (187661298043962145203/50000000000000000000)
  directionLo := (1891686419217127813/500000000000000000)
  directionHi := (378337283843425562601/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree064.table
  base := (-7728629060915056812788038239922872356739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-136992775206968422290754185651060000000000000)
      constant := (1348197101599019767071201218039819045000609305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree064.table
  base := (-1932533131536669399246646925390720483161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-70117435795521816927211578998970000000000000)
      constant := (708878126271885919569273756819195360232982390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1891686419217127813/500000000000000000)
  centralHi := (378337283843425562601/100000000000000000000)
  directionLo := (381328138953660696973/100000000000000000000)
  directionHi := (190664069476830348487/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree065.table
  base := (-7690399761385140385279360238658448341613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-139247045349020717831117767986000000000000000)
      constant := (1396900830559961297800846877159396879317322935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree065.table
  base := (-7691765090070573994264034852939909670139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-142539799489097104575469068025800000000000000)
      constant := (1468711093732868639427484102784066474739842305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (381328138953660696973/100000000000000000000)
  centralHi := (190664069476830348487/50000000000000000000)
  directionLo := (384295717865427118807/100000000000000000000)
  directionHi := (48036964733178389851/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree066.table
  base := (-478026526757695976496180932558001939327/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-23583552581845502228580225053490000000000000)
      constant := (241073343528423370469049651020824492744139640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree066.table
  base := (-1529932803866875676010078072232217756107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-48281575795716858432171659351220000000000000)
      constant := (506845677912557450455830162344478680136380775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384295717865427118807/100000000000000000000)
  centralHi := (48036964733178389851/12500000000000000000)
  directionLo := (96810138925871795603/25000000000000000000)
  directionHi := (387240555703487182413/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree067.table
  base := (-3801357123198231362186980788747353228549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-71877792816562654455922466327940000000000000)
      constant := (748407323983176871233840558780047671262720255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree067.table
  base := (-7603839421986002687169477861798176201309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-147149655285204046017560888081520000000000000)
      constant := (1573233941103019880272192840005888718501976455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96810138925871795603/25000000000000000000)
  centralHi := (387240555703487182413/100000000000000000000)
  directionLo := (390163167397163668741/100000000000000000000)
  directionHi := (195081583698581834371/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree068.table
  base := (-3776639617069286238673019800822702974699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3825000000000000000000000000000000000000000
      center := (6474)
      previous := (3471)
      next := (0)
      square := (94983292502203463779364424225000000000000)
      linear := (-4294407522799341307417897499730000000000000)
      constant := (45530131196005215565504219763386632224355265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree068.table
  base := (-7554300327867177678168646477864935050117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (12792)
      previous := (7098)
      next := (0)
      square := (189966585004406927558728848450000000000000)
      linear := (-8791446069603383337565105771140000000000000)
      constant := (95694217552695265739686052138625324686660495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390163167397163668741/100000000000000000000)
  centralHi := (195081583698581834371/50000000000000000000)
  directionLo := (393064048731537845499/100000000000000000000)
  directionHi := (786128097463075691/200000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree069.table
  base := (-3750064182053030237783300381642747857923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-24710687652871649998762016220960000000000000)
      constant := (266678230428885242901578713157079688035903795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree069.table
  base := (-937631850496448778977525912005020425057/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-25293251846885164576608784689540000000000000)
      constant := (280206700117469727569411120067233945829511620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393064048731537845499/100000000000000000000)
  centralHi := (786128097463075691/200000000000000000)
  directionLo := (79188735465865435817/20000000000000000000)
  directionHi := (197971838664663589543/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree070.table
  base := (-930408709155702456878535470768949131309/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-75259198029641097766467839830350000000000000)
      constant := (826474654586632192691041636089999266189305820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree070.table
  base := (-7444110057453598841656186212151829385213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-154064438979364458180698618165100000000000000)
      constant := (1736549354300973991589220345370965458845304935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79188735465865435817/20000000000000000000)
  centralHi := (197971838664663589543/50000000000000000000)
  directionLo := (398802513568949257869/100000000000000000000)
  directionHi := (39880251356894925787/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree071.table
  base := (-7382710360610130026787443457575095485457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-152772666201334491073299261995640000000000000)
      constant := (1706664146840353408601188556878161883211631715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree071.table
  base := (-461467032975605637485843794811802607853/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-78184683438708964450872264096480000000000000)
      constant := (896364537720617793331101674645803056678973880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398802513568949257869/100000000000000000000)
  centralHi := (39880251356894925787/10000000000000000000)
  directionLo := (80328200288753776193/20000000000000000000)
  directionHi := (200820500721884440483/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree072.table
  base := (-7318456875022936892500166412934526053333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-51675645447795595537887614776860000000000000)
      constant := (587071270569210307139583575708056829558801445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree072.table
  base := (-3659573984006643104088057704998849923761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-26445715795911899937131739703470000000000000)
      constant := (308296548216730133133309028758253985580496065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80328200288753776193/20000000000000000000)
  centralHi := (200820500721884440483/50000000000000000000)
  directionLo := (404459569367069315863/100000000000000000000)
  directionHi := (50557446170883664483/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree073.table
  base := (-7250514993563810602779975154690754090503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-157281206485439082154026426665520000000000000)
      constant := (1816598228644174510425040922513420743053008485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree073.table
  base := (-3625570759928556631006001507294672143717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-80489611336762435171918174124340000000000000)
      constant := (953849964508599110616636714938379788770960415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404459569367069315863/100000000000000000000)
  centralHi := (50557446170883664483/12500000000000000000)
  directionLo := (101814657731720029553/25000000000000000000)
  directionHi := (407258630926880118213/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree074.table
  base := (-717888989183767210653525612111837481489/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-79767738313745688847195004500230000000000000)
      constant := (936408665170621089339752788708075767766177775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree074.table
  base := (-7179457777444480737380058075722811920431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-163284150571578341064882258276540000000000000)
      constant := (1966490934842773315526294997716120830974794845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101814657731720029553/25000000000000000000)
  centralHi := (407258630926880118213/100000000000000000000)
  directionLo := (205019292797213571453/50000000000000000000)
  directionHi := (410038585594427142907/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree075.table
  base := (-7103586206886531194400792666958767358559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-53929915589847891078251197111800000000000000)
      constant := (643290352164700862951646444767983743500646735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree075.table
  base := (-888012605833754254242350017463372551771/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-27598179744938635297654694717400000000000000)
      constant := (337692042229991036376059971561310119952290860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205019292797213571453/50000000000000000000)
  centralHi := (410038585594427142907/100000000000000000000)
  directionLo := (412799819389640665893/100000000000000000000)
  directionHi := (206399909694820332947/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree076.table
  base := (-7024608093514985234536988164137108093449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-164044016911595968775117173670340000000000000)
      constant := (1987759353069521952178416147324932909244695755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree076.table
  base := (-175626859931013885072436057504359277811/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-83947003183842641253487039166130000000000000)
      constant := (1043341918452090113123246054274644151841358900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412799819389640665893/100000000000000000000)
  centralHi := (206399909694820332947/50000000000000000000)
  directionLo := (12985709547089396699/3125000000000000000)
  directionHi := (415542705506860694369/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree077.table
  base := (-3470979637359480759535313604519658354713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-83149143526824132157740378002640000000000000)
      constant := (1023241085824969117107913591401548843096957435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree077.table
  base := (-69423817093060279271753073621821170213/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-85099467132869376614009994180060000000000000)
      constant := (1074042821378562404751663021090317784068996750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12985709547089396699/3125000000000000000)
  centralHi := (415542705506860694369/100000000000000000000)
  directionLo := (52283450612951363043/12500000000000000000)
  directionHi := (83653520980722180869/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree078.table
  base := (-3427821543417584010826441937659926468183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-28092092865950093309307389723370000000000000)
      constant := (351006578141048757961639820318428218760426695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree078.table
  base := (-6856025715099422960930340496375390845703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-57501287387930741316355299462660000000000000)
      constant := (736785877601696725188679184439220680683877495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52283450612951363043/12500000000000000000)
  centralHi := (83653520980722180869/20000000000000000000)
  directionLo := (105243716713767748811/25000000000000000000)
  directionHi := (84194973371014199049/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree079.table
  base := (-6765662519964060912165100124577810749237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-170806827337752855396207920675160000000000000)
      constant := (2166431205772328460351144512436751571206172815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree079.table
  base := (-3383004518059799048951415674220857599973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-87404395030922847335055904207920000000000000)
      constant := (1136749886477741840714017087559100746912351135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105243716713767748811/25000000000000000000)
  centralHi := (84194973371014199049/20000000000000000000)
  directionLo := (211832414738329383589/50000000000000000000)
  directionHi := (423664829476658767179/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree080.table
  base := (-3336010127080625380530729662415788016953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-86530548739902575468285751505050000000000000)
      constant := (1113828673786961378245493649840282676839526235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree080.table
  base := (-667233401633447895994840946571598474271/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-88556858979949582695578859221850000000000000)
      constant := (1168756016362501227188541722659581809210528225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211832414738329383589/50000000000000000000)
  centralHi := (423664829476658767179/100000000000000000000)
  directionLo := (53292227527116927889/12500000000000000000)
  directionHi := (426337820216935423113/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree081.table
  base := (-1643679672960111028919867126532148304917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-29219227936976241079489180890840000000000000)
      constant := (381619643834614197090207167452707274196369610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree081.table
  base := (-3287501375915304732580034139660118505981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-29903107642992106018700604745260000000000000)
      constant := (400399064142340165126397664058134386276572365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53292227527116927889/12500000000000000000)
  centralHi := (426337820216935423113/100000000000000000000)
  directionLo := (214497078161434142047/50000000000000000000)
  directionHi := (85798831264573656819/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree082.table
  base := (-1618439996696154602426062597632665680997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-88784818881954871008649333839990000000000000)
      constant := (1176306362031834058488418303271686365637268030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree082.table
  base := (-6474017117289536050213443142555264669373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-181723573756006106833249538499420000000000000)
      constant := (2468146804962365779162975154437452782974804135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214497078161434142047/50000000000000000000)
  centralHi := (85798831264573656819/20000000000000000000)
  directionLo := (431634145279322346567/100000000000000000000)
  directionHi := (53954268159915293321/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree083.table
  base := (-6369146070120587799366165925718474366629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-179823907905962037557662250014920000000000000)
      constant := (2416341905627567341695992261037365240861989855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree083.table
  base := (-318468939481537803958591303285417352277/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-92014250827029788777147724263640000000000000)
      constant := (1267384635620819378185603921495658473336376150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431634145279322346567/100000000000000000000)
  centralHi := (53954268159915293321/12500000000000000000)
  directionLo := (434258085224504195347/100000000000000000000)
  directionHi := (108564521306126048837/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree084.table
  base := (-6260878673574926824586640234569340732989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-60692726016004777699341944116620000000000000)
      constant := (826968461726092918269010611491733907922492685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree084.table
  base := (-1565272317281146635850944723698391385141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-31055571592018841379223559759190000000000000)
      constant := (433710294030140741651722650533830946690827530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434258085224504195347/100000000000000000000)
  centralHi := (108564521306126048837/25000000000000000000)
  directionLo := (10921656633573679957/2500000000000000000)
  directionHi := (436866265342947198281/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree085.table
  base := (-6148959350295922350118082595502178353463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (12948)
      previous := (6942)
      next := (0)
      square := (189966585004406927558728848450000000000000)
      linear := (-10843085187650978155199377334400000000000000)
      constant := (149782537795124052096108837893590833559600805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree085.table
  base := (-3074574949122914641675880591234470254897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3825000000000000000000000000000000000000000
      center := (6396)
      previous := (3549)
      next := (0)
      square := (94983292502203463779364424225000000000000)
      linear := (-5548186983828427029305507899500000000000000)
      constant := (78547772538855825348394269076180630255003795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10921656633573679957/2500000000000000000)
  centralHi := (436866265342947198281/100000000000000000000)
  directionLo := (87891793247500860787/20000000000000000000)
  directionHi := (6866546347461004749/1562500000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree086.table
  base := (-3016694746748207156706523009365872348711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-93293359166059462089376498509870000000000000)
      constant := (1306267579762662375394938519143524830105013445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree086.table
  base := (-3016780939255053228161135239834569513069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-95471642674109994858716589305430000000000000)
      constant := (1369928381018344463010322289251439423482537655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87891793247500860787/20000000000000000000)
  centralHi := (6866546347461004749/1562500000000000000)
  directionLo := (221018230140851473551/50000000000000000000)
  directionHi := (442036460281702947103/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree087.table
  base := (-739271294143212168044853341537530051251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-31473498079028536619852763225780000000000000)
      constant := (446600236657845945602237988219588228911307660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree087.table
  base := (-184822696422151330434761371570255346591/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-32208035541045576739746514773120000000000000)
      constant := (468326539556591761110455744217596089160448240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221018230140851473551/50000000000000000000)
  centralHi := (442036460281702947103/100000000000000000000)
  directionLo := (444599011953714474831/100000000000000000000)
  directionHi := (27787438247107154677/6250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree088.table
  base := (-1447825762728690374563957398147785784061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-95547629308111757629740080844810000000000000)
      constant := (1373750954597515214217660576062608091756573390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree088.table
  base := (-2895722041167872362525955690708749666497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-97776570572163465579762499333290000000000000)
      constant := (1440465839852324661540070925037324710587206515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444599011953714474831/100000000000000000000)
  centralHi := (27787438247107154677/6250000000000000000)
  directionLo := (89429375630619438171/20000000000000000000)
  directionHi := (55893359769137148857/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree089.table
  base := (-5664788593557758546178752536753117708041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-193349528758275810799843744024560000000000000)
      constant := (2816236614176351271472730260037491704206926795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree089.table
  base := (-113298322631539675112194281283122873759/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-98929034521190200940285454347220000000000000)
      constant := (1476387038957026021711171487180907675669105125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89429375630619438171/20000000000000000000)
  centralHi := (55893359769137148857/12500000000000000000)
  directionLo := (8993606170027734659/2000000000000000000)
  directionHi := (449680308501386732951/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree090.table
  base := (-86478560701459820624702445859358417973/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-32600633150054684390034554393250000000000000)
      constant := (480967587189479248101900382272789800258785440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree090.table
  base := (-221389728240753645475665998449364092717/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-66720998980144624200538939574100000000000000)
      constant := (1008495473972557712385001631493650166451795125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8993606170027734659/2000000000000000000)
  centralHi := (449680308501386732951/100000000000000000000)
  directionLo := (226099772813764645231/50000000000000000000)
  directionHi := (452199545627529290463/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree091.table
  base := (-2700410868266537482207292048354807603899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-98929034521190200940285454347220000000000000)
      constant := (1478104312760799038625917819794228727111293505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree091.table
  base := (-1350231499552530585016340914731423414067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-101233962419243671661331364375080000000000000)
      constant := (1549534351354457694562796196293778677000117330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226099772813764645231/50000000000000000000)
  centralHi := (452199545627529290463/100000000000000000000)
  directionLo := (113676206359770365541/25000000000000000000)
  directionHi := (90940965087816292433/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree092.table
  base := (-1315842719371581653562104440709418797257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-100056169592216348710467245514690000000000000)
      constant := (1513722955924874407849181140473780017083345430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree092.table
  base := (-2631732564500968197278564599951295937171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-102386426368270407021854319389010000000000000)
      constant := (1586760456106805063203208387378345396337091145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113676206359770365541/25000000000000000000)
  centralHi := (90940965087816292433/20000000000000000000)
  directionLo := (4571963773800347419/1000000000000000000)
  directionHi := (457196377380034741901/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree093.table
  base := (-2561137981381089991857903418969822513239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-33727768221080832160216345560720000000000000)
      constant := (516586228933822617380562918334714819405108935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree093.table
  base := (-5122361155174314223075689217885850327831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-69025926878198094921584849601960000000000000)
      constant := (1082947681063611015615883614345602838828852615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4571963773800347419/1000000000000000000)
  centralHi := (457196377380034741901/100000000000000000000)
  directionLo := (229837212338031079109/50000000000000000000)
  directionHi := (459674424676062158219/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree094.table
  base := (-995507516214102661371921950689202253417/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-204620879468537288501661655699260000000000000)
      constant := (3172423003124986776573153952869890623471559575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree094.table
  base := (-2488807288123708396952154342265710266507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-104691354266323877742900229416870000000000000)
      constant := (1662517544572162228528385368235762437984076465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229837212338031079109/50000000000000000000)
  centralHi := (459674424676062158219/100000000000000000000)
  directionLo := (231069592283964498157/50000000000000000000)
  directionHi := (92427836913585799263/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree095.table
  base := (-241457813085912335074485891789315338541/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-103437574805294792021012619017100000000000000)
      constant := (1623081396766132768217786986416074540222742950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree095.table
  base := (-4829225840564617632462429657387105674231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-211687636430701226206846368861600000000000000)
      constant := (3402097044243378784335696611102430690706625845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231069592283964498157/50000000000000000000)
  centralHi := (92427836913585799263/20000000000000000000)
  directionLo := (464590868533758357553/100000000000000000000)
  directionHi := (232295434266879178777/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree096.table
  base := (-1169283120196115356484641417325726567067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-34854903292106979930398136728190000000000000)
      constant := (553456123105560588684337376354281950663529110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree096.table
  base := (-4677195350725398417946372928148147873207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-71330854776251565642630759629820000000000000)
      constant := (1160009634417396589815493438344509778969647655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464590868533758357553/100000000000000000000)
  centralHi := (232295434266879178777/50000000000000000000)
  directionLo := (467029682500795168619/100000000000000000000)
  directionHi := (23351484125039758431/5000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree097.table
  base := (-1130366666662490465631554958136192469393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-105691844947347087561376201352040000000000000)
      constant := (1698072416428594201296216171448244633871088070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree097.table
  base := (-4521523468437651271025037825364797684041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-216297492226808167648938188917320000000000000)
      constant := (3558830661466746275359822812497024806119046795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467029682500795168619/100000000000000000000)
  centralHi := (23351484125039758431/5000000000000000000)
  directionLo := (93891165409453756621/20000000000000000000)
  directionHi := (234727913523634391553/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree098.table
  base := (-2181079602474429624061401791272890438569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-106818980018373235331557992519510000000000000)
      constant := (1736193535594284265629651137093408059846410155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree098.table
  base := (-545276314856441221751957216797480374901/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-109301210062430819184992049472590000000000000)
      constant := (1819251157329235277368844241658267070897649980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93891165409453756621/20000000000000000000)
  centralHi := (234727913523634391553/50000000000000000000)
  directionLo := (5898368719936427523/1250000000000000000)
  directionHi := (471869497594914201841/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree099.table
  base := (-4199210443002679357415863360535344936501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-71964076726266255401159855791320000000000000)
      constant := (1183154483036862491802274170176161279700268165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree099.table
  base := (-4199256794430337084710420404642471180163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-73635782674305036363676669657680000000000000)
      constant := (1239681286341292450004329975270156887433993395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5898368719936427523/1250000000000000000)
  centralHi := (471869497594914201841/100000000000000000000)
  directionLo := (474270884592674884453/100000000000000000000)
  directionHi := (237135442296337442227/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree100.table
  base := (-4032620693791160643400805585952458207403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-218146500320851061743843149708900000000000000)
      constant := (3627373962552943736453787791436688281012723985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree100.table
  base := (-1008165639601999570078771431737162804779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-111606137960484289906037959500450000000000000)
      constant := (1900227645569804732778333116299516395447698210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474270884592674884453/100000000000000000000)
  centralHi := (237135442296337442227/50000000000000000000)
  directionLo := (29791260855754741951/6250000000000000000)
  directionHi := (476660173692075871217/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree101.table
  base := (-48279877993852964297137327038173872223/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-110200385231451678642103366021920000000000000)
      constant := (1853059303922852601119998011688284951669595400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree101.table
  base := (-1931214023938679507970124337878509100111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-112758601909511025266560914514380000000000000)
      constant := (1941368303961137221812002058019692989153056445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29791260855754741951/6250000000000000000)
  centralHi := (476660173692075871217/100000000000000000000)
  directionLo := (479037545914724243621/100000000000000000000)
  directionHi := (239518772957362121811/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree102.table
  base := (-3688519334746622289144192255830861156029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (4316)
      previous := (2314)
      next := (0)
      square := (63322195001468975852909616150000000000000)
      linear := (-4365785109901091231854319889780000000000000)
      constant := (74229360425056737933338487927067130405212605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree102.table
  base := (-3688553476548815586728700595349025723819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (4264)
      previous := (2366)
      next := (0)
      square := (63322195001468975852909616150000000000000)
      linear := (-4467100621903441593218975275620000000000000)
      constant := (77762506011618991772483756366649998440426155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479037545914724243621/100000000000000000000)
  centralHi := (239518772957362121811/50000000000000000000)
  directionLo := (30087698613272788081/6250000000000000000)
  directionHi := (481403177812364609297/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree103.table
  base := (-3511008209349863392769931320293093198169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-224909310747007948364933896713720000000000000)
      constant := (3866110281060393700725778529682842322957812155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree103.table
  base := (-14044156148858206882263184303625558151/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-115063529807564495987606824542240000000000000)
      constant := (2024954442321614763246759786066505702030780625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30087698613272788081/6250000000000000000)
  centralHi := (481403177812364609297/100000000000000000000)
  directionLo := (483757241619890106467/100000000000000000000)
  directionHi := (120939310404972526617/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree104.table
  base := (-3329857070966666368649079110757472521051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-227163580889060243905297479048660000000000000)
      constant := (3947357303292733980204961570398935069863731745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree104.table
  base := (-1664942451974940293953089905729054331271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-116215993756591231348129779556170000000000000)
      constant := (2067399919905203917066392727047561648421820645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483757241619890106467/100000000000000000000)
  centralHi := (120939310404972526617/25000000000000000000)
  directionLo := (48609990540168420817/10000000000000000000)
  directionHi := (486099905401684208171/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree105.table
  base := (-3145066107338646254722806027052578611971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-76472617010370846481887020461200000000000000)
      constant := (1343146148644444923156462361792977071717105715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree105.table
  base := (-1572545617039909049916353198424583517571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-39122819235205988902884244856700000000000000)
      constant := (703426778341348611898472782763254430451329715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48609990540168420817/10000000000000000000)
  centralHi := (486099905401684208171/100000000000000000000)
  directionLo := (488431333191645205501/100000000000000000000)
  directionHi := (244215666595822602751/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree106.table
  base := (-369579436043674596255871116314783680649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-115836060586582417493012321859270000000000000)
      constant := (2056176853386429966101366828070552952932639020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree106.table
  base := (-1478329084968001135351001798702418284989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-118520921654644702069175689584030000000000000)
      constant := (2153595686752629042945482677749083050203718055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488431333191645205501/100000000000000000000)
  centralHi := (244215666595822602751/50000000000000000000)
  directionLo := (245375842563611758041/50000000000000000000)
  directionHi := (490751685127223516083/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree107.table
  base := (-276456536785985144417827385549684598113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-116963195657608565263194113026740000000000000)
      constant := (2098051541905174013926558160354418759007702175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree107.table
  base := (-1382292920213192289836187753800644434053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-119673385603671437429698644597960000000000000)
      constant := (2197345974252729584323358843051189619135140735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245375842563611758041/50000000000000000000)
  centralHi := (490751685127223516083/100000000000000000000)
  directionLo := (246530558788890882489/50000000000000000000)
  directionHi := (493061117577781764979/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree108.table
  base := (-1284427942676147021503557544688380259879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-39363443576211571011125301398070000000000000)
      constant := (713447762538638659340855083562439871573424535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree108.table
  base := (-2568874362437718348279215918801934851983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-80550566368465448526814399741260000000000000)
      constant := (1494354131176194230903841964045161612416653695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246530558788890882489/50000000000000000000)
  centralHi := (493061117577781764979/100000000000000000000)
  directionLo := (15479993227111524971/3125000000000000000)
  directionHi := (495359783267568799073/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree109.table
  base := (-2369507167403035044424357151269038538673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-238434931599321721607115390723360000000000000)
      constant := (4366104179391186799013805505067472153804557635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree109.table
  base := (-2369523842088725328066828846776785641009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-243956627003449816301489109251640000000000000)
      constant := (4572302707194554681706556299872393902738677955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15479993227111524971/3125000000000000000)
  centralHi := (495359783267568799073/100000000000000000000)
  directionLo := (31102989462098831957/6250000000000000000)
  directionHi := (497647831393581311313/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree110.table
  base := (-2166519329001675110531027230971231637051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-240689201741374017147478973058300000000000000)
      constant := (4452355894792972800148517473184019132560151745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree110.table
  base := (-541633593962476858323774608021237728083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-123130777450751643511267509639750000000000000)
      constant := (2331206444124388129118429558032567606692561170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31102989462098831957/6250000000000000000)
  centralHi := (497647831393581311313/100000000000000000000)
  directionLo := (499925407738570467161/100000000000000000000)
  directionHi := (249962703869285233581/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree111.table
  base := (-1959892474733000184850341356191669668167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-80981157294475437562614185131080000000000000)
      constant := (1513147240025688272751248993761311111988496055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree111.table
  base := (-61247064110758164898134817671892058811/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-41427747133259459623930154884560000000000000)
      constant := (792232155924851558558879782647698566800869040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499925407738570467161/100000000000000000000)
  centralHi := (249962703869285233581/50000000000000000000)
  directionLo := (125548163694858937321/25000000000000000000)
  directionHi := (100438530955887149857/20000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree112.table
  base := (-1749626699835873026300510199078654089653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-245197742025478608228206137728180000000000000)
      constant := (4627361654004881443149762699575926103564062735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree112.table
  base := (-1749638949241626921579966036469394027077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-250871410697610228464626839335220000000000000)
      constant := (4845242848054245691034191782022819530677863615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125548163694858937321/25000000000000000000)
  centralHi := (100438530955887149857/20000000000000000000)
  directionLo := (504449711791234083467/100000000000000000000)
  directionHi := (126112427947808520867/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree113.table
  base := (-1535722091151982096866316675151501172239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-247452012167530903768569720063120000000000000)
      constant := (4716115695447046516388452526243668727255031805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree113.table
  base := (-767866571029019724762261063653573010739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-126588169297831849592836374681540000000000000)
      constant := (2468981312406655620520976868532252282995339305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504449711791234083467/100000000000000000000)
  centralHi := (126112427947808520867/25000000000000000000)
  directionLo := (506696714947019101441/100000000000000000000)
  directionHi := (253348357473509550721/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree114.table
  base := (-164772340996995290314379297773192577539/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-41617713718263866551488883733010000000000000)
      constant := (800950640562055551792935344691348840705473740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree114.table
  base := (-659094348435117531832489983381167348221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-42580211082286194984453109898490000000000000)
      constant := (838592044159429007842561023024978639545461965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506696714947019101441/100000000000000000000)
  centralHi := (253348357473509550721/50000000000000000000)
  directionLo := (15904181169178533239/3125000000000000000)
  directionHi := (508933797413713063649/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree115.table
  base := (-548498341408598425995932368705272410651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-125980276225817747424648442366500000000000000)
      constant := (2448063048418878649203904990429062932299483745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree115.table
  base := (-1097005674954376866845313451084609573901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-257786194391770640627764569418800000000000000)
      constant := (5126011767687137607921943104758194652491417495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15904181169178533239/3125000000000000000)
  centralHi := (508933797413713063649/100000000000000000000)
  directionLo := (3194756809026265263/625000000000000000)
  directionHi := (511161089444202442081/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree116.table
  base := (-87217602208252977818646296530005555739/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-127107411296843895194830233533970000000000000)
      constant := (2493691227489848735955508149089744388738071525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree116.table
  base := (-218046033139273807237882667741033747279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-130045561144912055674405239723330000000000000)
      constant := (2610670566136757247840658550835023712233273210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3194756809026265263/625000000000000000)
  centralHi := (511161089444202442081/100000000000000000000)
  directionLo := (513378718465837390269/100000000000000000000)
  directionHi := (51337871846583739027/10000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree117.table
  base := (-321858403344076820439638865514247530287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-42744848789290014321670674900480000000000000)
      constant := (846578819500989791214564380870264736956205855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree117.table
  base := (-643724121406071319759308025065049283387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-87465350062625860689952129824840000000000000)
      constant := (1772513452680995405573518485773601011356517355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513378718465837390269/100000000000000000000)
  centralHi := (51337871846583739027/10000000000000000000)
  directionLo := (515586809165505249573/100000000000000000000)
  directionHi := (257793404582752624787/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree118.table
  base := (-102904773152017640379090767349499957323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-129361681438896190735193815868910000000000000)
      constant := (2586198741094269613473757004630911506110028770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree118.table
  base := (-12863302786456837889845633116054920783/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-132350489042965526395451149751190000000000000)
      constant := (2707304722187832683359804373967243292083473360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (515586809165505249573/100000000000000000000)
  centralHi := (257793404582752624787/50000000000000000000)
  directionLo := (258892741785719403843/50000000000000000000)
  directionHi := (517785483571438807687/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree119.table
  base := (-175882931365751473518245305264456946421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (12948)
      previous := (6942)
      next := (0)
      square := (189966585004406927558728848450000000000000)
      linear := (-15351625471755569235926542004280000000000000)
      constant := (309773891168084480670721501496790690435987935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree119.table
  base := (-175888879850028022772142905720924087281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (12792)
      previous := (7098)
      next := (0)
      square := (189966585004406927558728848450000000000000)
      linear := (-15706229763763795500702835854720000000000000)
      constant := (324267552394069712654302646166641493073230035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258892741785719403843/50000000000000000000)
  centralHi := (517785483571438807687/100000000000000000000)
  directionLo := (103994972226382238079/20000000000000000000)
  directionHi := (129993715282977797599/25000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree120.table
  base := (12698325905015076279075806389561629951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-87743967720632324183704932135900000000000000)
      constant := (1786916306464904514956025393469093748329187925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree120.table
  base := (63486265821180031317837822494773545707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-89770277960679331410998039852700000000000000)
      constant := (1870452398827983025363887709732514843320639845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103994972226382238079/20000000000000000000)
  centralHi := (129993715282977797599/25000000000000000000)
  directionLo := (65269382348870123551/12500000000000000000)
  directionHi := (522155058790960988409/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree121.table
  base := (306504546165196212622945025406908081977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-265486173303949268091478378742640000000000000)
      constant := (5456175790229462071998172622403942839606110885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree121.table
  base := (306499710086492902272776249556087385059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-271615761780091464954040029585960000000000000)
      constant := (5711035861238881785245138196720122916442692295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65269382348870123551/12500000000000000000)
  centralHi := (522155058790960988409/100000000000000000000)
  directionLo := (524326191061283458337/100000000000000000000)
  directionHi := (262163095530641729169/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree122.table
  base := (553155777915488912858619571950903751307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-267740443446001563631841961077580000000000000)
      constant := (5552436761833169969787042491928805503285747535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree122.table
  base := (553151417855034343082581096035077395181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-273920689678144935675085939613820000000000000)
      constant := (5811584384507626396991203950311680181524328905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524326191061283458337/100000000000000000000)
  centralHi := (262163095530641729169/50000000000000000000)
  directionLo := (52648837009441635429/10000000000000000000)
  directionHi := (526488370094416354291/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree123.table
  base := (200861321769762121433431273776589422417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-44999118931342309862034257235420000000000000)
      constant := (941588638952598164792818522849972030292355390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree123.table
  base := (50215084777744652261832653553695611631/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36244)
      previous := (20111)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-46037602929366401066021974940280000000000000)
      constant := (985500460977523654658669918592791163811363080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52648837009441635429/10000000000000000000)
  centralHi := (526488370094416354291/100000000000000000000)
  directionLo := (264320852874171055411/50000000000000000000)
  directionHi := (528641705748342110823/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree124.table
  base := (105737303861604880222359276959825062189/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-136124491865053077356284562873730000000000000)
      constant := (2873730502710513095049906369922160624668839725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree124.table
  base := (528684747672014232971043623133876793671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-139265272737125938558588879834770000000000000)
      constant := (3007645502457328735650272377887504067701691355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264320852874171055411/50000000000000000000)
  centralHi := (528641705748342110823/100000000000000000000)
  directionLo := (33174144103288854889/6250000000000000000)
  directionHi := (21231452226104867129/4000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree125.table
  base := (328734749971981897688898823289335238537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-137251626936079225126466354041200000000000000)
      constant := (2923112138262508535736972641048130609554347370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree125.table
  base := (657467903005190451022803477761748949693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-140417736686152673919111834848700000000000000)
      constant := (3059224550642472680082644858005166545090757465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33174144103288854889/6250000000000000000)
  centralHi := (21231452226104867129/4000000000000000000)
  directionLo := (53292227527116927889/10000000000000000000)
  directionHi := (532922275271169278891/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree126.table
  base := (394035785106959645832377649838402181809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (36686)
      previous := (19669)
      next := (0)
      square := (538238657512486294749731737275000000000000)
      linear := (-46126254002368457632216048402890000000000000)
      constant := (990970274438556716193994312646954946916284030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree126.table
  base := (1576140261674323500149604312107165400483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-94380133756786272853089859908420000000000000)
      constant := (2074159018209293108042826345444536562011093805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53292227527116927889/10000000000000000000)
  centralHi := (532922275271169278891/100000000000000000000)
  directionLo := (267524858981385841273/50000000000000000000)
  directionHi := (535049717962771682547/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree127.table
  base := (920492715867317188087487007985086904447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (110058)
      previous := (59007)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-139505897078131520666829936376140000000000000)
      constant := (3023126557684669222591920464319273055192333235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree127.table
  base := (1840982837175375694353155644668036033431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217464)
      previous := (120666)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-285445329168412289280315489753120000000000000)
      constant := (6327374864616247313430571204398921808614770155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267524858981385841273/50000000000000000000)
  centralHi := (535049717962771682547/100000000000000000000)
  directionLo := (268584367519725132027/50000000000000000000)
  directionHi := (107433747007890052811/20000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree128.table
  base := (421893169417585946714608820492565951217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (220116)
      previous := (118014)
      next := (0)
      square := (3229431945074917768498390423650000000000000)
      linear := (-281266064298315336874023455087220000000000000)
      constant := (6147518682391512905543045606932433100977885425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree128.table
  base := (263682938601318092408710905112749103973/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (108732)
      previous := (60333)
      next := (0)
      square := (1614715972537458884249195211825000000000000)
      linear := (-143875128533232880000680699890490000000000000)
      constant := (3216571265470895953708906914538877208388675460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell013.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268584367519725132027/50000000000000000000)
  centralHi := (107433747007890052811/20000000000000000000)
  directionLo := (269639712911379543909/50000000000000000000)
  directionHi := (539279425822759087819/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree129.table
  base := (476316872276410254493429229995173293559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (73372)
      previous := (39338)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-94506778146789210804795679140720000000000000)
      constant := (2083206115790454798631643052224907381137891325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree129.table
  base := (2381582254199285656856976519574713370553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (72488)
      previous := (40222)
      next := (0)
      square := (1076477315024972589499463474550000000000000)
      linear := (-96685061654839743574135769936280000000000000)
      constant := (2179926684437818039550255935233718382461347255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell013.Kernel129
