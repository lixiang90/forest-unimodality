import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell023.Parameters
import ForestUnimodality.BinomialMassData.Q65_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q65_153.Batch050_099
import ForestUnimodality.BinomialMassData.Q65_153.Batch100_149
import ForestUnimodality.BinomialMassData.Q65_153.Batch150_199
import ForestUnimodality.BinomialMassData.Q22_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q22_51.Batch050_099
import ForestUnimodality.BinomialMassData.Q22_51.Batch100_149
import ForestUnimodality.BinomialMassData.Q22_51.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree000.table
  base := (2439874030800902364845228523/100000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (77396790291435497988192792600000000000000)
      constant := (12443357557084602060710665467300000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree000.table
  base := (2439874030800902364845228523/100000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (25798930097145165996064264200000000000000)
      constant := (4147785852361534020236888489100000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree001.table
  base := (152825224396231552295726407348367905506429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (1648078418112030248815491606000000000000000)
      constant := (209646358620608392396371193293202605882352733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree001.table
  base := (37857465315598036986886634585621388141313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (182364892747906389702805539480000000000000)
      constant := (23079354892756893896360086580320289542483556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49431818042324279781/100000000000000000000)
  directionHi := (24715909021162139891/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree002.table
  base := (49332264415148538545693206359680436477423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (1206443498355302051949777811800000000000000)
      constant := (134460728131642186708133117054559922058822942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree002.table
  base := (48510618196919325504902082307423977423213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (132539414621506285441032701160000000000000)
      constant := (14686914750984610052599577504951737091503178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49431818042324279781/100000000000000000000)
  centralHi := (24715909021162139891/50000000000000000000)
  directionLo := (69907147488214053033/100000000000000000000)
  directionHi := (34953573744107026517/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree003.table
  base := (13204330092528977411461449692455144933111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (84978730955397095009340446400000000000000)
      constant := (9899194955893189942480707803228185873829915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree003.table
  base := (64550632651117768042629672834395353837593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (9190437388345131242139984760000000000000)
      constant := (1074720576107802452629395806504721015239081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69907147488214053033/100000000000000000000)
  centralHi := (34953573744107026517/50000000000000000000)
  directionLo := (85618420359805567813/100000000000000000000)
  directionHi := (42809210179902783907/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree004.table
  base := (11483432572674184311821577908245524853821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (323173658841845658218350223400000000000000)
      constant := (61200581188247717428029968562616350894846068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree004.table
  base := (8948229739375572350183073801182348293657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (32888458368706076917487024520000000000000)
      constant := (6616700290098929453403563659824496444647605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/100000000000000000000)
  centralHi := (42809210179902783907/50000000000000000000)
  directionLo := (49431818042324279781/50000000000000000000)
  directionHi := (98863636084648559563/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree005.table
  base := (1660582494870344553331424969149140290709/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-118461260914882538647363570800000000000000)
      constant := (43638791826997231254348755432867323606125860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree005.table
  base := (32282154371821847348961382205667055272219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-16937019757694027344285813800000000000000)
      constant := (4707033651998278219604501457467059456649507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49431818042324279781/50000000000000000000)
  centralHi := (98863636084648559563/100000000000000000000)
  directionLo := (110532905394037666001/100000000000000000000)
  directionHi := (55266452697018833001/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree006.table
  base := (12429761934562989564353374376506186528179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-62232908963512303945897485000000000000000)
      constant := (3586894700521341035099696127210893077622774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree006.table
  base := (12070670530062364881437723811245194565527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-7418055320454903511784294680000000000000)
      constant := (386615783605227125106873237262336615227918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110532905394037666001/100000000000000000000)
  centralHi := (55266452697018833001/50000000000000000000)
  directionLo := (60541365630898881203/50000000000000000000)
  directionHi := (121082731261797762407/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree007.table
  base := (19136348806289020238176059132805298566771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-1001731100428338932378791159200000000000000)
      constant := (24733000940131252506685431858372896126443667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree007.table
  base := (18575654472735204678146231039822250922029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-116587976010494235867831490440000000000000)
      constant := (2667538185220377612355402558372804391070437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60541365630898881203/50000000000000000000)
  centralHi := (121082731261797762407/100000000000000000000)
  directionLo := (26156859478757149407/20000000000000000000)
  directionHi := (32696074348446436759/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree008.table
  base := (15025922398071241754162156578424397496171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-1443366020185067129244504953400000000000000)
      constant := (19592327151309068900229380352490395352227467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree008.table
  base := (14578346962799142624292198287569618404339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-166413454136894340129604328760000000000000)
      constant := (2116989660349596869801456998478151615863867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26156859478757149407/20000000000000000000)
  centralHi := (32696074348446436759/25000000000000000000)
  directionLo := (139814294976428106067/100000000000000000000)
  directionHi := (34953573744107026517/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree009.table
  base := (2982777260884595150445185226698062116243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-69814849627473900967045138800000000000000)
      constant := (593991674657001416385682565746404671713572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree009.table
  base := (462547002776267411487786574881068236657/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-24026548029254938265708574120000000000000)
      constant := (193141969812832619582207072404454000579225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139814294976428106067/100000000000000000000)
  centralHi := (34953573744107026517/25000000000000000000)
  directionLo := (9268465882935802459/6250000000000000000)
  directionHi := (29659090825394567869/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree010.table
  base := (4748780779621370794513639908226088240773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-2326635859698523522975932541800000000000000)
      constant := (13581409061813684253847337647254647015088842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree010.table
  base := (1148394302249772912517139816869178240927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-266064410389694548653150005400000000000000)
      constant := (1478696279810441378562996371847874166894648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9268465882935802459/6250000000000000000)
  centralHi := (29659090825394567869/20000000000000000000)
  directionLo := (156317133896750300929/100000000000000000000)
  directionHi := (15631713389675030093/10000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree011.table
  base := (469502476097251051214975053458908609263/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-2768270779455251719841646336000000000000000)
      constant := (11929596758388826961102694002306674479282416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree011.table
  base := (3621520002313472902332384000861067827119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-315889888516094652914922843720000000000000)
      constant := (1306766329230596575427271864583486755098414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156317133896750300929/100000000000000000000)
  centralHi := (15631713389675030093/10000000000000000000)
  directionLo := (32789358630302007243/20000000000000000000)
  directionHi := (20493349143938754527/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree012.table
  base := (730463090983326495444136653815574108047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-356656188801331101856373347800000000000000)
      constant := (1211352633765811219167414364270262708249528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree012.table
  base := (5605794104326036568219867233395721976863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-40635040738054973019632853560000000000000)
      constant := (133697844961779769250150562487727273606671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32789358630302007243/20000000000000000000)
  centralHi := (20493349143938754527/12500000000000000000)
  directionLo := (85618420359805567813/50000000000000000000)
  directionHi := (171236840719611135627/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree013.table
  base := (275636151651836936919458092939957887371/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-3651540618968708113573073924400000000000000)
      constant := (10385704753747053973845542870153152174557872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree013.table
  base := (1049153563673177843385890406707932857551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-415540844768894861438468520360000000000000)
      constant := (1156182329339085556794641210985254908821212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/50000000000000000000)
  centralHi := (171236840719611135627/100000000000000000000)
  directionLo := (4455723864775153631/2500000000000000000)
  directionHi := (178228954591006145241/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree014.table
  base := (394734304654862987456082253342665004517/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-4093175538725436310438787718600000000000000)
      constant := (10306401605893581313376332526822797689759272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree014.table
  base := (2964244294466101072069789736109100126567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-465366322895294965700241358680000000000000)
      constant := (1157629310606886496326522909144692319364751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4455723864775153631/2500000000000000000)
  centralHi := (178228954591006145241/100000000000000000000)
  directionLo := (92478463559864015899/50000000000000000000)
  directionHi := (184956927119728031799/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree015.table
  base := (128160239988819762593167365638253651139/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-503867828720240500811611279200000000000000)
      constant := (1179375226315459722213227563582444937988272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree015.table
  base := (468482987147128243495058615179995958801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-57243533446855007773557133000000000000000)
      constant := (133589383375065973367199737832239725198468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92478463559864015899/50000000000000000000)
  centralHi := (184956927119728031799/100000000000000000000)
  directionLo := (191448608050677252451/100000000000000000000)
  directionHi := (47862152012669313113/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree016.table
  base := (1062693656361180791091566498573874624747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-4976445378238892704170215307000000000000000)
      constant := (11274444596132678069687891980536225358276619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree016.table
  base := (225259552115844720002742414856238490081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-565017279148095174223787035320000000000000)
      constant := (1286437980329932414242084705412017955929572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191448608050677252451/100000000000000000000)
  centralHi := (47862152012669313113/25000000000000000000)
  directionLo := (1581818177354376953/800000000000000000)
  directionHi := (98863636084648559563/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree017.table
  base := (17545409269120624976833997206696797033/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-5418080297995620901035929101200000000000000)
      constant := (12260703197205016539156395284036214895144410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree017.table
  base := (1706726791136614050473033774217127631/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-614842757274495278485559873640000000000000)
      constant := (1407236817318727974439156804759283528440688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1581818177354376953/800000000000000000)
  centralHi := (98863636084648559563/50000000000000000000)
  directionLo := (203812607054815809951/100000000000000000000)
  directionHi := (6369143970462994061/3125000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree018.table
  base := (-19548784847606257966586656046182759947/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-217026489546383299922283070200000000000000)
      constant := (501974644985859947334758109332629735766496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree018.table
  base := (-761335189285501985247018591511192846411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-73852026155655042527481412440000000000000)
      constant := (173616380597537751608067259464309721611013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203812607054815809951/100000000000000000000)
  centralHi := (6369143970462994061/3125000000000000000)
  directionLo := (2097214424646421591/1000000000000000000)
  directionHi := (209721442464642159101/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree019.table
  base := (-675883881630939770341444059339740112921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-6301350137509077294767356689600000000000000)
      constant := (15136561697033469580392724637078355729015566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree019.table
  base := (-73805509766273079502632666810986151469/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-714493713527295487009105550280000000000000)
      constant := (1750653152163727897237751471878382376504860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2097214424646421591/1000000000000000000)
  centralHi := (209721442464642159101/100000000000000000000)
  directionLo := (1683346089390485227/781250000000000000)
  directionHi := (215468299441982109057/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree020.table
  base := (-50311562502615367293982669889612624709/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-6742985057265805491633070483800000000000000)
      constant := (16997640559630982039177580322480136631028280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree020.table
  base := (-1063098620495699840382459475618973601763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-764319191653695591270878388600000000000000)
      constant := (1970149480392347248987790976460594077860522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1683346089390485227/781250000000000000)
  centralHi := (215468299441982109057/100000000000000000000)
  directionLo := (110532905394037666001/50000000000000000000)
  directionHi := (221065810788075332003/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree021.table
  base := (-261537497484639558720392832893264127603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-798291108558059298722087142000000000000000)
      constant := (2125100919496614476772176296173305884767410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree021.table
  base := (-679813426798356849402718755142569700761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-90460518864455077281405691880000000000000)
      constant := (246651647864938979474220414730305260348252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110532905394037666001/50000000000000000000)
  centralHi := (221065810788075332003/100000000000000000000)
  directionLo := (9061001916729392683/4000000000000000000)
  directionHi := (56631261979558704269/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree022.table
  base := (-633405969861119520308146094430085339433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-7626254896779261885364498072200000000000000)
      constant := (21512380385225211444989226299848862438003795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree022.table
  base := (-101929868604611455402533587258649707413/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-863970147906495799794424065240000000000000)
      constant := (2498808344523387255737875093261651032505952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9061001916729392683/4000000000000000000)
  centralHi := (56631261979558704269/25000000000000000000)
  directionLo := (231855778382441950787/100000000000000000000)
  directionHi := (57963944595610487697/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree023.table
  base := (-459124219254076936847357985395136744587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-8067889816535990082230211866400000000000000)
      constant := (24149391638630131916763898769387173621629608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree023.table
  base := (-3759233443718386058031004640188040597447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-913795626032895904056196903560000000000000)
      constant := (2806133941054677536124775643331229788590609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231855778382441950787/100000000000000000000)
  centralHi := (57963944595610487697/25000000000000000000)
  directionLo := (118533335611018612321/50000000000000000000)
  directionHi := (237066671222037224643/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree024.table
  base := (-4138051114127187734224831071650967137827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-945502748476968697677325073400000000000000)
      constant := (3003372653591327981865838902037402027912469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree024.table
  base := (-527054931943751335267453719034066906219/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-107069011573255112035329971320000000000000)
      constant := (349012715720218950842178189891366900754216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118533335611018612321/50000000000000000000)
  centralHi := (237066671222037224643/100000000000000000000)
  directionLo := (242165462523595524813/100000000000000000000)
  directionHi := (121082731261797762407/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree025.table
  base := (-1141583687199600225663307558329000606343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-8951159656049446475961639454800000000000000)
      constant := (30149576224249758980594558631223864660262756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree025.table
  base := (-185499064438885160183736191652477704317/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1013446582285696112579742580200000000000000)
      constant := (3503122120445423970516231726929272780987475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242165462523595524813/100000000000000000000)
  centralHi := (121082731261797762407/50000000000000000000)
  directionLo := (247159090211621398907/100000000000000000000)
  directionHi := (61789772552905349727/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree026.table
  base := (-4961426698014454043466303503002165841559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-9392794575806174672827353249000000000000000)
      constant := (33502126195377343265405036888366017636173257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree026.table
  base := (-1256474220018952024616372609498867892257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1063272060412096216841515418520000000000000)
      constant := (3891613526521104512754466112906692849938716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247159090211621398907/100000000000000000000)
  centralHi := (61789772552905349727/25000000000000000000)
  directionLo := (50410760958035878867/20000000000000000000)
  directionHi := (7876681399693106073/3125000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree027.table
  base := (-213057545839660319670835739401781325619/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-364238129465292698877521001600000000000000)
      constant := (1373471074316261156343772689762728809835775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree027.table
  base := (-5384781285146418318142019042545394484289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-123677504282055146789254250760000000000000)
      constant := (478457473699927835563692068596728293767087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50410760958035878867/20000000000000000000)
  centralHi := (7876681399693106073/3125000000000000000)
  directionLo := (256855261079416703439/100000000000000000000)
  directionHi := (3210690763492708793/1250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree028.table
  base := (-5664077749716569994744923009521819467157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-10276064415319631066558780837400000000000000)
      constant := (40890626902563773868861036099888454593724811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree028.table
  base := (-5716805724794514867355385268349565157163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1162923016664896425365061095160000000000000)
      constant := (4746223918292747046301462856822516530954061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256855261079416703439/100000000000000000000)
  centralHi := (3210690763492708793/1250000000000000000)
  directionLo := (261568594787571494071/100000000000000000000)
  directionHi := (32696074348446436759/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree029.table
  base := (-29883507891128185102269292113291431549/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-10717699335076359263424494631600000000000000)
      constant := (44919603510888943383116410158499539751405400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree029.table
  base := (-6024296174072806091587652373503519702099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1212748494791296529626833933480000000000000)
      constant := (5211577617318229714580413152773961485578853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261568594787571494071/100000000000000000000)
  centralHi := (32696074348446436759/12500000000000000000)
  directionLo := (266198486874201126759/100000000000000000000)
  directionHi := (6654962171855028169/2500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree030.table
  base := (-1253272922451921718105508876299456136183/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1239926028314787495587800936200000000000000)
      constant := (5463091090170482346973743189630916055820005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree030.table
  base := (-6309275543925167787280275902652612824541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-140285996990855181543178530200000000000000)
      constant := (633540983889042836450504089654905581982803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266198486874201126759/100000000000000000000)
  centralHi := (6654962171855028169/2500000000000000000)
  directionLo := (135374609001359340733/50000000000000000000)
  directionHi := (270749218002718681467/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree031.table
  base := (-1306971598148978972275443679677236765723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-11600969174589815657155922220000000000000000)
      constant := (53632809406198300302424597689922224867997145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree031.table
  base := (-3286751897984968326726911714186294708577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1312399451044096738150379610120000000000000)
      constant := (6216828357214608971773686980578993819175438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135374609001359340733/50000000000000000000)
  centralHi := (270749218002718681467/100000000000000000000)
  directionLo := (275224714885951225239/100000000000000000000)
  directionHi := (6880617872148780631/2500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree032.table
  base := (-6783743716149325219353793082843353005171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-12042604094346543854021636014200000000000000)
      constant := (58312421417482619857093930444924702911879533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree032.table
  base := (-6818512479211160669476341294843708968149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1362224929170496842412152448440000000000000)
      constant := (6756221796960280704894552583168912527873203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275224714885951225239/100000000000000000000)
  centralHi := (6880617872148780631/2500000000000000000)
  directionLo := (139814294976428106067/50000000000000000000)
  directionHi := (55925717990571242427/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree033.table
  base := (-280575369080852846206576278919697007257/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1387137668233696894543038867600000000000000)
      constant := (7022753307500680377118661911632158947241975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree033.table
  base := (-440352161097127977209733635963775682087/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-156894489699655216297102809640000000000000)
      constant := (813316136411211548223991509737853014472336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139814294976428106067/50000000000000000000)
  centralHi := (55925717990571242427/20000000000000000000)
  directionLo := (141982087738200319733/50000000000000000000)
  directionHi := (283964175476400639467/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree034.table
  base := (-7227968044388676108646198704888682325389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-12925873933860000247753063602600000000000000)
      constant := (68308247862813539346690938067368284437939347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree034.table
  base := (-7256030369894534343848240385977194055603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1461875885423297050935698125080000000000000)
      constant := (7907521126765400329846097367665489309492741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141982087738200319733/50000000000000000000)
  centralHi := (283964175476400639467/100000000000000000000)
  directionLo := (14411727653976943521/5000000000000000000)
  directionHi := (288234553079538870421/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree035.table
  base := (-7425532059234541413468640381202260496847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-13367508853616728444618777396800000000000000)
      constant := (73621397904521068328500009947584487295841681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree035.table
  base := (-7450709872753969540376614614421638558567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1511701363549697155197470963400000000000000)
      constant := (8519094961626003534335390619993489300539249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14411727653976943521/5000000000000000000)
  centralHi := (288234553079538870421/100000000000000000000)
  directionLo := (58488515872410702407/20000000000000000000)
  directionHi := (73110644840513378009/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree036.table
  base := (-1521596185513444581548366353157354651159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-511449769384202097832758933000000000000000)
      constant := (2931221636344639748163613535944874563954455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree036.table
  base := (-1907638084592523258045754216427920253337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-173502982408455251051027089080000000000000)
      constant := (1017159134076704372997305941762901422773084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58488515872410702407/20000000000000000000)
  centralHi := (73110644840513378009/25000000000000000000)
  directionLo := (9268465882935802459/3125000000000000000)
  directionHi := (296590908253945678689/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree037.table
  base := (-1555220792760952280825053158448998526659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-14250778693130184838350204985200000000000000)
      constant := (84871919807212511763411482866578645143952785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree037.table
  base := (-7796323206711577033803259389863768309373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1611352319802497363721016640040000000000000)
      constant := (9813415749643200948943206661030843448665931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9268465882935802459/3125000000000000000)
  centralHi := (296590908253945678689/100000000000000000000)
  directionLo := (150341005296184812283/50000000000000000000)
  directionHi := (300682010592369624567/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree038.table
  base := (-3965294932001606945794111747399134935903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-14692413612886913035215918779400000000000000)
      constant := (90807256447773593543671062151662782386523138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree038.table
  base := (-993586106348829127950960126688028910727/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1661177797928897467982789478360000000000000)
      constant := (10495943635413719954047088335013852613270152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150341005296184812283/50000000000000000000)
  centralHi := (300682010592369624567/100000000000000000000)
  directionLo := (60943638266463657297/20000000000000000000)
  directionHi := (152359095666159143243/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree039.table
  base := (-4036019771401562517312261983208206537893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1681560948071515692453514730400000000000000)
      constant := (10772018515947609837576479381638288799404742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree039.table
  base := (-4044114703226518087603857747009174015559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-190111475117255285804951368520000000000000)
      constant := (1244658567024165863413872125881688083470994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60943638266463657297/20000000000000000000)
  centralHi := (152359095666159143243/50000000000000000000)
  directionLo := (308701604731508954121/100000000000000000000)
  directionHi := (154350802365754477061/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree040.table
  base := (-2050244332171132367813636673535937834917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-15575683452400369428947346367800000000000000)
      constant := (103293928394160189050409177162164054405277164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree040.table
  base := (-2053862484428583270793018234164262069681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1760828754181697676506335155000000000000000)
      constant := (11931288878260140770007476408691471613355228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308701604731508954121/100000000000000000000)
  centralHi := (154350802365754477061/50000000000000000000)
  directionLo := (312634267793500601859/100000000000000000000)
  directionHi := (15631713389675030093/5000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree041.table
  base := (-2079465182291025696083127657396847563987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-16017318372157097625813060162000000000000000)
      constant := (109843911711818232802743390837558163617559604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree041.table
  base := (-4165395077420581894096603454248049781903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1810654232308097780768107993320000000000000)
      constant := (12683961684870868025669024766520096766737682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312634267793500601859/100000000000000000000)
  centralHi := (15631713389675030093/5000000000000000000)
  directionLo := (39564759025897123149/12500000000000000000)
  directionHi := (316518072207176985193/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree042.table
  base := (-4211544474785480584901738283177986246553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1828772587990425091408752661800000000000000)
      constant := (12955285210084936310374956305347536208554782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree042.table
  base := (-843463287348649520801458722267104190857/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-206719967826055320558875647960000000000000)
      constant := (1495542994694974511032749258334592287554310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39564759025897123149/12500000000000000000)
  centralHi := (316518072207176985193/100000000000000000000)
  directionLo := (20022174686448932451/6250000000000000000)
  directionHi := (320354794983182919217/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree043.table
  base := (-8517010325045138163987909162315269899529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-16900588211670554019544487750400000000000000)
      constant := (123554414273510944842789545059991873348348567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree043.table
  base := (-8527311378374963978753063509964746870539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1910305188560897989291653669960000000000000)
      constant := (14259013687848979085558754090655393728807533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20022174686448932451/6250000000000000000)
  centralHi := (320354794983182919217/100000000000000000000)
  directionLo := (162073053978511968017/50000000000000000000)
  directionHi := (64829221591404787207/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree044.table
  base := (-4299964402359448824311759688041255787513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-17342223131427282216410201544600000000000000)
      constant := (130714035322102659585835377783134381561189198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree044.table
  base := (-344364633345012351739060189289653231027/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-1960130666687298093553426508280000000000000)
      constant := (15081297496543326464421673112287076391321725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162073053978511968017/50000000000000000000)
  centralHi := (64829221591404787207/20000000000000000000)
  directionLo := (327893586303020072431/100000000000000000000)
  directionHi := (20493349143938754527/6250000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree045.table
  base := (-8672109609137357528012127936374236801103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-658661409303111496787996864400000000000000)
      constant := (5113928326957368284010685102744913923143747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree045.table
  base := (-8680298863267376824159673859343034556793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-223328460534855355312799927400000000000000)
      constant := (1769633302984582902063484628391168412534519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327893586303020072431/100000000000000000000)
  centralHi := (20493349143938754527/6250000000000000000)
  directionLo := (331598716182112998003/100000000000000000000)
  directionHi := (82899679045528249501/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree046.table
  base := (-8733784166435710695085167312020560419227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-18225492970940738610141629133000000000000000)
      constant := (145640184114207636476582322523347688302724421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree046.table
  base := (-1748216081888295493030250450505370067159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2059781622940098302076972184920000000000000)
      constant := (16795186727655270710672471472083391898623365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331598716182112998003/100000000000000000000)
  centralHi := (82899679045528249501/25000000000000000000)
  directionLo := (335262901628848557627/100000000000000000000)
  directionHi := (83815725407212139407/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree047.table
  base := (-4392577209639514291016117590126571923779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-18667127890697466807007342927200000000000000)
      constant := (153406115106128934648591776029291420921912634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree047.table
  base := (-879165196181276855839767301292078771597/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2109607101066498406338745023240000000000000)
      constant := (17686729201006631090907198297503119479456590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335262901628848557627/100000000000000000000)
  centralHi := (83815725407212139407/25000000000000000000)
  directionLo := (67777494153609556717/20000000000000000000)
  directionHi := (169443735384023891793/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree048.table
  base := (-8826396582808512703350656862698373328239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2123195867828243889319228524600000000000000)
      constant := (17930401683929267077650449036007148880779433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree048.table
  base := (-4416090119802005889021113358057344071303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-239936953243655390066724206840000000000000)
      constant := (2066811293208249413681290963746050301575698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67777494153609556717/20000000000000000000)
  centralHi := (169443735384023891793/50000000000000000000)
  directionLo := (85618420359805567813/25000000000000000000)
  directionHi := (342473681439222271253/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree049.table
  base := (-8857664423590562145224100488354974760819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-19550397730210923200738770515600000000000000)
      constant := (169542472525349112085694207394035199754352237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree049.table
  base := (-1107851299637690059193477189702411463927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2209258057319298614862290699880000000000000)
      constant := (19538881832652305664877908264924248368153352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/25000000000000000000)
  centralHi := (342473681439222271253/100000000000000000000)
  directionLo := (346022726296269958469/100000000000000000000)
  directionHi := (34602272629626995847/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree050.table
  base := (-1109886515079055263138489143971579336267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-19992032649967651397604484309800000000000000)
      constant := (177912502451593055632216261290009082031682728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree050.table
  base := (-4441834407155989069910238927856561476861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2259083535445698719124063538200000000000000)
      constant := (20499450446199791341425444108075892188080534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346022726296269958469/100000000000000000000)
  centralHi := (34602272629626995847/10000000000000000000)
  directionLo := (21845983590066891573/6250000000000000000)
  directionHi := (349535737441070265169/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree051.table
  base := (-4445398380869631348992393194296763811819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2270407507747153288274466456000000000000000)
      constant := (20720393744909733078898781863045190273583386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree051.table
  base := (-8894865526461794119196887602000378706577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-256545445952455424820648486280000000000000)
      constant := (2386998960458562347044079353645993561988191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21845983590066891573/6250000000000000000)
  centralHi := (349535737441070265169/100000000000000000000)
  directionLo := (7060275812840239623/2000000000000000000)
  directionHi := (353013790642011981151/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree052.table
  base := (-1778576104338696305752876328019413298531/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-20875302489481107791335911898200000000000000)
      constant := (195255455588457294197351930021586339439614065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree052.table
  base := (-8896496339080079768629778827553242193839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2358734491698498927647609214840000000000000)
      constant := (22489487768188160973177950482264353944342633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7060275812840239623/2000000000000000000)
  centralHi := (353013790642011981151/100000000000000000000)
  directionLo := (4455723864775153631/1250000000000000000)
  directionHi := (356457909182012290481/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree053.table
  base := (-8885432562812092574703497567475602332789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-21316937409237835988201625692400000000000000)
      constant := (204228115327891644387322329296086095587749547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree053.table
  base := (-4444322334678150179526647530958741575657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2408559969824899031909382053160000000000000)
      constant := (23518929055553102704316229046406625077848958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4455723864775153631/1250000000000000000)
  centralHi := (356457909182012290481/100000000000000000000)
  directionLo := (71973813475008027583/20000000000000000000)
  directionHi := (89967266843760034479/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree054.table
  base := (-8868530693266790939237020807749424972389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-805873049222020895743234795800000000000000)
      constant := (7903756140023637930465570210804779326408161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree054.table
  base := (-443569157459857638893963576510582954689/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-273153938661255459574572765720000000000000)
      constant := (2730144821504462410337504342866401795405740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71973813475008027583/20000000000000000000)
  centralHi := (89967266843760034479/25000000000000000000)
  directionLo := (18162409689269664361/5000000000000000000)
  directionHi := (363248193785393287221/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree055.table
  base := (-4421121407020965021707790817466060232527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-22200207248751292381933053280800000000000000)
      constant := (222775263447041578742309411321198470119620642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree055.table
  base := (-8844775020822567329731732469622001599891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2508210926077699240432927729800000000000000)
      constant := (25646601106089688602734404892147833755216677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18162409689269664361/5000000000000000000)
  centralHi := (363248193785393287221/100000000000000000000)
  directionLo := (22912260886242088697/6250000000000000000)
  directionHi := (366596174179873419153/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree056.table
  base := (-8806628181469747079123455403801676843083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-22641842168508020578798767075000000000000000)
      constant := (232349576731132217633314729020965090987074709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree056.table
  base := (-8808875351749544042543372791371919473541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2558036404204099344694700568120000000000000)
      constant := (26744813767871582429133124144040096320548227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22912260886242088697/6250000000000000000)
  centralHi := (366596174179873419153/100000000000000000000)
  directionLo := (369913854239456063597/100000000000000000000)
  directionHi := (184956927119728031799/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree057.table
  base := (-8761738508848696477857614426736332708679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2564830787584972086184942318800000000000000)
      constant := (26902698269299796560379446435209341095572113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree057.table
  base := (-4381866046268963844102400266774980271283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-289762431370055494328497045160000000000000)
      constant := (3096214893605576324681603756849650670776378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369913854239456063597/100000000000000000000)
  centralHi := (184956927119728031799/50000000000000000000)
  directionLo := (373202042053977784699/100000000000000000000)
  directionHi := (3732020420539777847/1000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree058.table
  base := (-8707618927654787404894393777933452526713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-23525112008021476972530194663400000000000000)
      constant := (252099324378696968352024764611785635870716199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree058.table
  base := (-544336687352956669701693045570427433609/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2657687360456899553218246244760000000000000)
      constant := (29009955541393185049116139720923593642525168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373202042053977784699/100000000000000000000)
  centralHi := (3732020420539777847/1000000000000000000)
  directionLo := (376461510420691558829/100000000000000000000)
  directionHi := (37646151042069155883/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree059.table
  base := (-2161077206560437002404126554851611725489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-23966746927778205169395908457600000000000000)
      constant := (262274642358365531897443973632377322616006588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree059.table
  base := (-2161469106780193243186035620037878379909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2707512838583299657480019083080000000000000)
      constant := (30176872701613983757160754391256818431495692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376461510420691558829/100000000000000000000)
  centralHi := (37646151042069155883/10000000000000000000)
  directionLo := (94923249741303472233/25000000000000000000)
  directionHi := (379692998965213888933/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree060.table
  base := (-8571842581644946958476210608347154873613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2712042427503881485140180250200000000000000)
      constant := (30294465669502906336218653836922885304337211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree060.table
  base := (-4286616022259315167207378308359840635121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-306370924078855529082421324600000000000000)
      constant := (3485186742065317394844275801515765418405886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94923249741303472233/25000000000000000000)
  centralHi := (379692998965213888933/100000000000000000000)
  directionLo := (382897216101354504903/100000000000000000000)
  directionHi := (47862152012669313113/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree061.table
  base := (-4245125099056908830247380342326950733759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-24850016767291661563127336046000000000000000)
      constant := (283225929064327373933374230911731577679227714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree061.table
  base := (-4245740712264591739438504189213633154567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2807163794836099866003564759720000000000000)
      constant := (32579375253387492822597697370420628254702498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382897216101354504903/100000000000000000000)
  centralHi := (47862152012669313113/12500000000000000000)
  directionLo := (77214968168907983489/20000000000000000000)
  directionHi := (193037420422269958723/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree062.table
  base := (-8399557864260997284852836868245053638737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-25291651687048389759993049840200000000000000)
      constant := (294001820413049581237701215832426561139459151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree062.table
  base := (-8400648581946076671083846552287786338147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2856989272962499970265337598040000000000000)
      constant := (33814952751749464991620598697179968690263509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77214968168907983489/20000000000000000000)
  centralHi := (193037420422269958723/50000000000000000000)
  directionLo := (97306631122995121109/25000000000000000000)
  directionHi := (389226524491980484437/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree063.table
  base := (-2074947109800295356251733518988065362947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-953084689140930294698472727200000000000000)
      constant := (11295475318321920115065157251626434665958812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree063.table
  base := (-4150377216094430186710717384399265962799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-322979416787655563836345604040000000000000)
      constant := (3897045552623842426658011462050424957264834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97306631122995121109/25000000000000000000)
  centralHi := (389226524491980484437/100000000000000000000)
  directionLo := (392352892181357241107/100000000000000000000)
  directionHi := (98088223045339310277/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree064.table
  base := (-8190961876730598196453478129860914156611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-26174921526561846153724477428600000000000000)
      constant := (316153941132876753425509742439181521206346653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree064.table
  base := (-4095908596113220594656769040122618500087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-2956640229215300178788883274680000000000000)
      constant := (36354744131786600657178374701242478738973378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392352892181357241107/100000000000000000000)
  centralHi := (98088223045339310277/25000000000000000000)
  directionLo := (395454544338594238251/100000000000000000000)
  directionHi := (98863636084648559563/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree065.table
  base := (-807309559544441052843194120162311737831/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-26616556446318574350590191222800000000000000)
      constant := (327530119042198772840389952587864967370067130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree065.table
  base := (-4036926364808242152232454522391531057317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3006465707341700283050656113000000000000000)
      constant := (37658952798529198669976586184148191496460998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395454544338594238251/100000000000000000000)
  centralHi := (98863636084648559563/25000000000000000000)
  directionLo := (24908253626513310543/6250000000000000000)
  directionHi := (398532058024212968689/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree066.table
  base := (-7946204801682787346529337440149511778477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3006465707341700283050656113000000000000000)
      constant := (37678482931503054304540728639657124697893019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree066.table
  base := (-7946874866375631963273033513143239618447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-339587909496455598590269883480000000000000)
      constant := (4331781539897092179435991363556564926486401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24908253626513310543/6250000000000000000)
  centralHi := (398532058024212968689/100000000000000000000)
  directionLo := (200792994093409611593/50000000000000000000)
  directionHi := (401585988186819223187/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree067.table
  base := (-3905151385659052599650981689047073718169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-27499826285832030744321618811200000000000000)
      constant := (350882604875986638619577537620864358980162574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree067.table
  base := (-3905447821763187690941892233319713628771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3106116663594500491574201789640000000000000)
      constant := (40335985471144052335950064398684167629596074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200792994093409611593/50000000000000000000)
  centralHi := (401585988186819223187/100000000000000000000)
  directionLo := (80923373766286725391/20000000000000000000)
  directionHi := (101154217207858406739/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree068.table
  base := (-7665401095629401713606512377562470529871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-27941461205588758941187332605400000000000000)
      constant := (362858878558384987664341225420096478080367633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree068.table
  base := (-766592555140985431773700533110954727751/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3155942141720900595835974627960000000000000)
      constant := (41708806029717672450166716520020239266540970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80923373766286725391/20000000000000000000)
  centralHi := (101154217207858406739/25000000000000000000)
  directionLo := (407625214109631619903/100000000000000000000)
  directionHi := (6369143970462994061/1562500000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree069.table
  base := (-234734684245047963268602726775961428769/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3153677347260609682005894044400000000000000)
      constant := (41670572610421767388716988908204892844746976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree069.table
  base := (-3755986865097602443966725673539079208999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-356196402205255633344194162920000000000000)
      constant := (4789388237372090236850829231579671306894034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407625214109631619903/100000000000000000000)
  centralHi := (6369143970462994061/1562500000000000000)
  directionLo := (102652879834448774359/25000000000000000000)
  directionHi := (410611519337795097437/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree070.table
  base := (-7348638010323058895111794408827790957713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-28824731045102215334918760193800000000000000)
      constant := (387411417511785895764277053579044131851229199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree070.table
  base := (-1469809628888532394804775157950990527121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3255593097973700804359520304600000000000000)
      constant := (44523048572459755443545038840167492246752435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102652879834448774359/25000000000000000000)
  centralHi := (410611519337795097437/100000000000000000000)
  directionLo := (103394065487296565827/25000000000000000000)
  directionHi := (413576261949186263309/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree071.table
  base := (-7176793157927748904624478291123909285853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-29266365964858943531784473988000000000000000)
      constant := (399987659983493307315085637617622376913380419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree071.table
  base := (-7177155735078417018798542545075389382037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3305418576100100908621293142920000000000000)
      constant := (45964468276088795095082533413323465424548339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103394065487296565827/25000000000000000000)
  centralHi := (413576261949186263309/100000000000000000000)
  directionLo := (104129975596256440553/25000000000000000000)
  directionHi := (416519902385025762213/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree072.table
  base := (-3497991040260254688039992725748876426979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-1100296329059839693653710658600000000000000)
      constant := (15287550800939635837880782221973614604448142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree072.table
  base := (-3498151275852315970816611990106171233123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-372804894914055668098118442360000000000000)
      constant := (5269861369071866701400605959056390178073818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104129975596256440553/25000000000000000000)
  centralHi := (416519902385025762213/100000000000000000000)
  directionLo := (419442884929284318201/100000000000000000000)
  directionHi := (209721442464642159101/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree073.table
  base := (-6806210667340825978073950010581128238049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-30149635804372399925515901576400000000000000)
      constant := (425740044327933704921707312521929786416206527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree073.table
  base := (-3403246933894827342887192226475754040291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3405069532352901117144838819560000000000000)
      constant := (48915899902293113860797090447978419263670954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419442884929284318201/100000000000000000000)
  centralHi := (209721442464642159101/50000000000000000000)
  directionLo := (422345638491473357869/100000000000000000000)
  directionHi := (42234563849147335787/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree074.table
  base := (-6607484063518739056213439540458075884753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-30591270724129128122381615370600000000000000)
      constant := (438916171006339853655963283156789229506695119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree074.table
  base := (-6607734280954092860821870325568272396941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3454895010479301221406611657880000000000000)
      constant := (50425910314591782775388667369308054323268027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422345638491473357869/100000000000000000000)
  centralHi := (42234563849147335787/10000000000000000000)
  directionLo := (85045715468267949239/20000000000000000000)
  directionHi := (106307144335334936549/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree075.table
  base := (-1279961352952648715960807709424876193301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3448100627098428479916369907200000000000000)
      constant := (50254693941110814194757249114789969712124735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree075.table
  base := (-6400027800281642246205336356023816684761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-389413387622855702852042721800000000000000)
      constant := (5773198105017000178014160801947595116359063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85045715468267949239/20000000000000000000)
  centralHi := (106307144335334936549/25000000000000000000)
  directionLo := (85618420359805567813/20000000000000000000)
  directionHi := (214046050899513919533/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree076.table
  base := (-6183182699985555416421512626305508657561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-31474540563642584516113042959000000000000000)
      constant := (465868262308795382962611359925577314578538503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree076.table
  base := (-6183377922333919780645717190983307570319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3554545966732101429930157334520000000000000)
      constant := (53514517259002842949389126991699553941741193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/20000000000000000000)
  centralHi := (214046050899513919533/50000000000000000000)
  directionLo := (430936598883964218113/100000000000000000000)
  directionHi := (215468299441982109057/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree077.table
  base := (-5957615303395035898555543832245717039229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-31916175483399312712978756753200000000000000)
      constant := (479644216793827728730513344645497647636981667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree077.table
  base := (-1191557539466242637762687109091993937437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3604371444858501534191930172840000000000000)
      constant := (55093112789457602795299132016424624637860695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430936598883964218113/100000000000000000000)
  centralHi := (215468299441982109057/50000000000000000000)
  directionLo := (433762442925442920127/100000000000000000000)
  directionHi := (6777538170710045627/1562500000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree078.table
  base := (-572310757740955268045150977237242581533/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3595312267017337878871607838600000000000000)
      constant := (54846678310084995699625034580827018850254510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree078.table
  base := (-715407473346481278473084948944878556657/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-406021880331655737605967001240000000000000)
      constant := (6299396569923115221447200611263496516294648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (433762442925442920127/100000000000000000000)
  centralHi := (6777538170710045627/1562500000000000000)
  directionLo := (17462799845505534877/4000000000000000000)
  directionHi := (218284998068819185963/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree079.table
  base := (-5479662147551025326496701044788706929001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-32799445322912769106710184341600000000000000)
      constant := (507795922684263397420785960517825950558765623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree079.table
  base := (-1095959302719633882566423132932981704231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3704022401111301742715475849480000000000000)
      constant := (58318885923143967749729429497226268996263285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17462799845505534877/4000000000000000000)
  centralHi := (218284998068819185963/50000000000000000000)
  directionLo := (43935960916154666387/10000000000000000000)
  directionHi := (439359609161546663871/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree080.table
  base := (-1306820327586918621782218131248893958441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-33241080242669497303575898135800000000000000)
      constant := (522171667312003677267342504053081092076906972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree080.table
  base := (-2613699952936835914099272704957853693161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3753847879237701846977248687800000000000000)
      constant := (59966062860671679399523855352282896769892734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43935960916154666387/10000000000000000000)
  centralHi := (439359609161546663871/100000000000000000000)
  directionLo := (110532905394037666001/25000000000000000000)
  directionHi := (88426324315230132801/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree081.table
  base := (-4965967075134285323822661300072471104443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-1247507968978749092608948590000000000000000)
      constant := (19879530959523400061812754317196303973673407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree081.table
  base := (-4966071734811091191511565228040958320521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-422630373040455772359891280680000000000000)
      constant := (6848455518988402631512340090803303708551143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110532905394037666001/25000000000000000000)
  centralHi := (88426324315230132801/20000000000000000000)
  directionLo := (27805397648807407377/6250000000000000000)
  directionHi := (444886362380918518033/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree082.table
  base := (-4695721200528184594637313250809615197573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-34124350082182953697307325724200000000000000)
      constant := (551522926048031711679743966473635159872941979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree082.table
  base := (-4695813547882434721030964367282835479037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3853498835490502055500794364440000000000000)
      constant := (63328996117052583497597298137085726171707339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27805397648807407377/6250000000000000000)
  centralHi := (444886362380918518033/100000000000000000000)
  directionLo := (447624150451576291789/100000000000000000000)
  directionHi := (44762415045157629179/10000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree083.table
  base := (-220827261312975053053171352666145361467/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-34565985001939681894173039518400000000000000)
      constant := (566498435614495019995168749404074356745198820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree083.table
  base := (-883325339529485880469119353445869388387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3903324313616902159762567202760000000000000)
      constant := (65044751992200920612687472659093909917883945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447624150451576291789/100000000000000000000)
  centralHi := (44762415045157629179/10000000000000000000)
  directionLo := (450345294970942117803/100000000000000000000)
  directionHi := (112586323742735529451/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree084.table
  base := (-4128440500947784801322963612709000468037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-3889735546855156676782083701400000000000000)
      constant := (64630429194385845128611897243255522928390339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree084.table
  base := (-2064256183427218219075550773335727031381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-439238865749255807113815560120000000000000)
      constant := (7420374123931126196096572399786585280933046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (450345294970942117803/100000000000000000000)
  centralHi := (112586323742735529451/25000000000000000000)
  directionLo := (453050095836469634151/100000000000000000000)
  directionHi := (56631261979558704269/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree085.table
  base := (-3831408206341592049355875814185125173733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-35449254841453138287904467106800000000000000)
      constant := (597049205825696708232623628706367082635769659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree085.table
  base := (-3831471590296186066982122859391622200441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4002975269869702368286112879400000000000000)
      constant := (68544841328266941227646534398513081803332527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453050095836469634151/100000000000000000000)
  centralHi := (56631261979558704269/12500000000000000000)
  directionLo := (45573884404602135727/10000000000000000000)
  directionHi := (455738844046021357271/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree086.table
  base := (-3525449378471793032549878042270408979413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-35890889761209866484770180901000000000000000)
      constant := (612624463416552817917405527247793646835348299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree086.table
  base := (-35255052738402557440706578305397785161/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4052800747996102472547885717720000000000000)
      constant := (70329174492263597650369125500247413887036700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45573884404602135727/10000000000000000000)
  centralHi := (455738844046021357271/100000000000000000000)
  directionLo := (91682364412655334293/20000000000000000000)
  directionHi := (229205911031638335733/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree087.table
  base := (-3210564926111904778423875509507012149933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4036947186774066075737321632800000000000000)
      constant := (69822181585628866918328804259545427141060251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree087.table
  base := (-3210614210999865650338977986924204460739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-455847358458055841867739839560000000000000)
      constant := (8015151831773620260595090817742288524167437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91682364412655334293/20000000000000000000)
  centralHi := (229205911031638335733/50000000000000000000)
  directionLo := (461069304164073243837/100000000000000000000)
  directionHi := (230534652082036621919/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree088.table
  base := (-57735112937772382201976442194934303511/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-36774159600723322878501608489400000000000000)
      constant := (644374717289685706634847208458878773203267650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree088.table
  base := (-2886799097363250856280554080569513277907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4152451704248902681071431394360000000000000)
      constant := (73966417202938895346821108951752864468480229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461069304164073243837/100000000000000000000)
  centralHi := (230534652082036621919/50000000000000000000)
  directionLo := (231855778382441950787/50000000000000000000)
  directionHi := (18548462270595356063/4000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree089.table
  base := (-638505560335488632119698697282960895709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-37215794520480051075367322283600000000000000)
      constant := (660549711508986925551324523661865451386434828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree089.table
  base := (-319257567894834847745811733224358272979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4202277182375302785333204232680000000000000)
      constant := (75819326549827611739494120790053385473873704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231855778382441950787/50000000000000000000)
  centralHi := (18548462270595356063/4000000000000000000)
  directionLo := (93267767746908492437/20000000000000000000)
  directionHi := (233169419367271231093/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree090.table
  base := (-2212365325196294848254647232278625996937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-1394719608897658491564186521400000000000000)
      constant := (25071282077063369722280069571153790074156213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree090.table
  base := (-13827494276227007855426723555986862767/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-472455851166855876621664119000000000000000)
      constant := (8632788271627752803718412963927715733273760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93267767746908492437/20000000000000000000)
  centralHi := (233169419367271231093/50000000000000000000)
  directionLo := (468951401690250902789/100000000000000000000)
  directionHi := (46895140169025090279/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree091.table
  base := (-930892720035138299615626907425027898521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-38099064359993507469098749872000000000000000)
      constant := (693499430259049014984017960721451473167473166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree091.table
  base := (-930907595698486233868819314330372594939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4301928138628102993856749909320000000000000)
      constant := (79593720815354504318162880565334905985948666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468951401690250902789/100000000000000000000)
  centralHi := (46895140169025090279/10000000000000000000)
  directionLo := (471549490278825891/100000000000000000)
  directionHi := (471549490278825891001/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree092.table
  base := (-1502283062824431197153670091345318662947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-38540699279750235665964463666200000000000000)
      constant := (710274153387364071239211829064217496201121981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree092.table
  base := (-375577319772606667040214255923990119323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4351753616754503098118522747640000000000000)
      constant := (81515205598549340472786912449454518046974324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471549490278825891/100000000000000000)
  centralHi := (471549490278825891001/100000000000000000000)
  directionLo := (118533335611018612321/25000000000000000000)
  directionHi := (94826668488814889857/20000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree093.table
  base := (-1133858613720135645222623575268693759177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4331370466611884873647797495600000000000000)
      constant := (80805420542995137237081786851483889854845919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree093.table
  base := (-141735214030333716946986891797387935879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-489064343875655911375588398440000000000000)
      constant := (9273283193154943095343311534235555240720456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118533335611018612321/25000000000000000000)
  centralHi := (94826668488814889857/20000000000000000000)
  directionLo := (95340637936225164711/20000000000000000000)
  directionHi := (119175797420281455889/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree094.table
  base := (-756512463541304933372083512935180040679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-39423969119263692059695891254600000000000000)
      constant := (744423324247256055726451642866688257083985017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree094.table
  base := (-756532812750441211972307838330277981931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4451404573007303306642068424280000000000000)
      constant := (85426750185639745324147152745055467468764557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95340637936225164711/20000000000000000000)
  centralHi := (119175797420281455889/25000000000000000000)
  directionLo := (95851851455697793851/20000000000000000000)
  directionHi := (59907407159811121157/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree095.table
  base := (-185122469905479209800133852786046149109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-39865604039020420256561605048800000000000000)
      constant := (761797771017264335361394966761927228905353814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree095.table
  base := (-370262864923791990468012072036060428337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4501230051133703410903841262600000000000000)
      constant := (87416809896785675084311917968978482754464439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95851851455697793851/20000000000000000000)
  centralHi := (59907407159811121157/12500000000000000000)
  directionLo := (60225220568568999929/12500000000000000000)
  directionHi := (481801764548551999433/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree096.table
  base := (24943667782048123598541548557836933931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4478582106530794272603035427000000000000000)
      constant := (86596902755342168848871269624929349050891443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree096.table
  base := (6231969934586937887353849481537396513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-505672836584455946129512677880000000000000)
      constant := (9936636425928104535715977803844744542962884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60225220568568999929/12500000000000000000)
  centralHi := (481801764548551999433/100000000000000000000)
  directionLo := (484330925047191049627/100000000000000000000)
  directionHi := (121082731261797762407/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree097.table
  base := (429053102645527048917385609752152741917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-40748873878533876650293032637200000000000000)
      constant := (797146385236374166171449340407128714325619709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree097.table
  base := (214519599194082911710994439679721862751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4600881007386503619427386939240000000000000)
      constant := (91465503961245827270372127731021994890001806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484330925047191049627/100000000000000000000)
  centralHi := (121082731261797762407/25000000000000000000)
  directionLo := (121711736695777733711/25000000000000000000)
  directionHi := (97369389356622186969/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree098.table
  base := (21052078428698077940835423863384175783/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-41190508798290604847158746431400000000000000)
      constant := (815120552018699623392497347070395200402127640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree098.table
  base := (10525886165061712628726075958750976379/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4650706485512903723689159777560000000000000)
      constant := (93524138250197763473224602247015111950878960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121711736695777733711/25000000000000000000)
  centralHi := (97369389356622186969/20000000000000000000)
  directionLo := (97870006483499674247/20000000000000000000)
  directionHi := (122337508104374592809/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree099.table
  base := (1264033569007147321594454037505035265721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-1541931248816567890519424452800000000000000)
      constant := (30862763883944942768102218245412756798551771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree099.table
  base := (7900142426485437766131202179204698079/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-522281329293255980883436957320000000000000)
      constant := (10622847852587583085083658493607436778774880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97870006483499674247/20000000000000000000)
  centralHi := (122337508104374592809/25000000000000000000)
  directionLo := (245920189727265054323/50000000000000000000)
  directionHi := (491840379454530108647/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree100.table
  base := (847452109068725365689831434750487711947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-42073778637804061240890174019800000000000000)
      constant := (851668603531837583934424488671302843158702038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree100.table
  base := (847447363327052723543333735325982854853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4750357441765703932212705454200000000000000)
      constant := (97709981206521944448559942163009750753585018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245920189727265054323/50000000000000000000)
  centralHi := (491840379454530108647/100000000000000000000)
  directionLo := (247159090211621398907/50000000000000000000)
  directionHi := (98863636084648559563/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree101.table
  base := (2134694923896025375815872634604777217979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-42515413557560789437755887814000000000000000)
      constant := (870242487793466864403185678992350778229157083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree101.table
  base := (2134686568343543262558945084002046010101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4800182919892104036474478292520000000000000)
      constant := (99837189828461916427573455955772313039545453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247159090211621398907/50000000000000000000)
  centralHi := (98863636084648559563/20000000000000000000)
  directionLo := (15524488220351204731/3125000000000000000)
  directionHi := (496783623051238551393/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree102.table
  base := (2583405542678450099709256722519882059237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4773005386368613070513511289800000000000000)
      constant := (98779586383739778690482396038545541955063261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree102.table
  base := (2583398187827775343619477805831869066641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-538889822002056015637361236760000000000000)
      constant := (11331917391101110872950064519019141774132897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15524488220351204731/3125000000000000000)
  centralHi := (496783623051238551393/100000000000000000000)
  directionLo := (499236890430669728157/100000000000000000000)
  directionHi := (249618445215334864079/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree103.table
  base := (3041035945818583094832799734488214930603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-43398683397074245831487315402400000000000000)
      constant := (907989972335237738097963544530890271959440331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree103.table
  base := (1520514736220156576777716787497855363639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4899833876144904244998023969160000000000000)
      constant := (104160181263628215989374253003854343741273534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499236890430669728157/100000000000000000000)
  centralHi := (249618445215334864079/50000000000000000000)
  directionLo := (250839080588459136031/50000000000000000000)
  directionHi := (501678161176918272063/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree104.table
  base := (3507586017754160096343514322473327325149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-43840318316830974028353029196600000000000000)
      constant := (927163572279076816161362825966045771726730173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree104.table
  base := (3507580320739252405580240280168779944607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4949659354271304349259796807480000000000000)
      constant := (106355964044095959470166127420785823331524871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250839080588459136031/50000000000000000000)
  centralHi := (501678161176918272063/100000000000000000000)
  directionLo := (50410760958035878867/10000000000000000000)
  directionHi := (504107609580358788671/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree105.table
  base := (3983055654424293434066941955077864354639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-4920217026287522469468749221200000000000000)
      constant := (105170786349098155564745464361626913246259767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree105.table
  base := (159322025644943990662550123865096604613/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-555498314710856050391285516200000000000000)
      constant := (12063844983033141813217476862642666056960525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50410760958035878867/10000000000000000000)
  centralHi := (504107609580358788671/100000000000000000000)
  directionLo := (506525405751570273757/100000000000000000000)
  directionHi := (253262702875785136879/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree106.table
  base := (4467444761869374147108142236152103914581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-44723588156344430422084456785000000000000000)
      constant := (966110486794275108322850271471181447090378037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree106.table
  base := (4467440350626790370221316153244923479997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5049310310524104557783342484120000000000000)
      constant := (110816103660541282111206193684566473292439541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506525405751570273757/100000000000000000000)
  centralHi := (253262702875785136879/50000000000000000000)
  directionLo := (508931715760338870589/100000000000000000000)
  directionHi := (50893171576033887059/10000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree107.table
  base := (4960753255007637415074353978022133735587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-45165223076101158618950170579200000000000000)
      constant := (985883801119094350724105270460236478153903299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree107.table
  base := (4960749373864523213700120116867507260681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5099135788650504662045115322440000000000000)
      constant := (113080460472291178793476353355160728610884193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508931715760338870589/100000000000000000000)
  centralHi := (50893171576033887059/10000000000000000000)
  directionLo := (511326701768773085213/100000000000000000000)
  directionHi := (255663350884386542607/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree108.table
  base := (2731490528282965304939512066758415910313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-1689142888735477289474662384200000000000000)
      constant := (37253963704071703559911073802809358422851926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree108.table
  base := (2731488821058500012506284633073778729351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-572106807419656085145209795640000000000000)
      constant := (12818630585781537470017074292244508476797934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511326701768773085213/100000000000000000000)
  centralHi := (255663350884386542607/50000000000000000000)
  directionLo := (256855261079416703439/50000000000000000000)
  directionHi := (513710522158833406879/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree109.table
  base := (5974128096145084387950903671453443956779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-46048492915614615012681598167600000000000000)
      constant := (1026030143369860388317233828202091392328484683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree109.table
  base := (23896500370112915268603600623723249553/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5198786744903304870568660999080000000000000)
      constant := (117677748050152290647225951702577414295402250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256855261079416703439/50000000000000000000)
  centralHi := (513710522158833406879/100000000000000000000)
  directionLo := (129020832913640037113/25000000000000000000)
  directionHi := (516083331654560148453/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree110.table
  base := (1623548577350695924862055048366697769659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-46490127835371343209547311961800000000000000)
      constant := (1046403171110268159499377656446403771315281772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree110.table
  base := (6494191667407295647594704312064417568057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5248612223029704974830433837400000000000000)
      constant := (120010678797819829211487580075745855887912721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129020832913640037113/25000000000000000000)
  centralHi := (516083331654560148453/100000000000000000000)
  directionLo := (2025176880622134509/390625000000000000)
  directionHi := (103689056287853286861/20000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree111.table
  base := (7023179637339013873100798413934771640281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5214640306125341267379225084000000000000000)
      constant := (118552900349990698829076827337832020060962993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree111.table
  base := (1755794328404615055980696629870941247117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-588715300128456119899134075080000000000000)
      constant := (13596274167434076073133123431311224004803956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2025176880622134509/390625000000000000)
  centralHi := (103689056287853286861/20000000000000000000)
  directionLo := (520796519267947524671/100000000000000000000)
  directionHi := (8137445613561680073/1562500000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree112.table
  base := (1512216805134211520251323681688167316331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-47373397674884799603278739550200000000000000)
      constant := (1087748939414057476471538365548423031972938935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree112.table
  base := (3780540991024315248695204324927027813511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5348263179282505183353979514040000000000000)
      constant := (124745114169898553903899599187107670510934366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520796519267947524671/100000000000000000000)
  centralHi := (8137445613561680073/1562500000000000000)
  directionLo := (261568594787571494071/50000000000000000000)
  directionHi := (523137189575142988143/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree113.table
  base := (405395371214333854396757726652872287307/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-47815032594641527800144453344400000000000000)
      constant := (1108721679833687169083853231158520102792434780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree113.table
  base := (8107905627142250964839002053272213235841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5398088657408905287615752352360000000000000)
      constant := (127146618779825436956608783988230648625083673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261568594787571494071/50000000000000000000)
  centralHi := (523137189575142988143/100000000000000000000)
  directionLo := (21018697343138981493/4000000000000000000)
  directionHi := (262733716789237268663/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree114.table
  base := (1732729957353112542070661213873703099181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5361851946044250666334463015400000000000000)
      constant := (125543813816098288994229301464613382870873465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree114.table
  base := (8663648206494927520931242043480153125407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-605323792837256154653058354520000000000000)
      constant := (14396775703355495724245450512019162603131919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21018697343138981493/4000000000000000000)
  centralHi := (262733716789237268663/50000000000000000000)
  directionLo := (527787389378069553261/100000000000000000000)
  directionHi := (263893694689034776631/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree115.table
  base := (9228311069960392222450249645186947931781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-48698302434154984193875880932800000000000000)
      constant := (1151266872888235909331344057833922427302062437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree115.table
  base := (9228309680498233148514333442570336268871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5497739613661705496139298029000000000000000)
      constant := (132018201814960538255076033384713261449137263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527787389378069553261/100000000000000000000)
  centralHi := (263893694689034776631/50000000000000000000)
  directionLo := (530097192052068374363/100000000000000000000)
  directionHi := (132524298013017093591/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree116.table
  base := (9801891233629946304029371698689834463413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-49139937353911712390741594727000000000000000)
      constant := (1172839325408328935229783528241095902056119701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree116.table
  base := (9801890012029115078324667206767429189493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5547565091788105600401070867320000000000000)
      constant := (134488280228428840093512388134155416665992429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530097192052068374363/100000000000000000000)
  centralHi := (132524298013017093591/25000000000000000000)
  directionLo := (266198486874201126759/50000000000000000000)
  directionHi := (532396973748402253519/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree117.table
  base := (10384390240117687641252347250772397890083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-1836354528654386688429900315600000000000000)
      constant := (44244877105678171361563953737289392292394233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree117.table
  base := (10384389166178174071110103317149767840327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-621932285546056189406982633960000000000000)
      constant := (15220135173918136549990282381511546053285559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266198486874201126759/50000000000000000000)
  centralHi := (532396973748402253519/100000000000000000000)
  directionLo := (534686863773018435721/100000000000000000000)
  directionHi := (267343431886509217861/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree118.table
  base := (10975808054070049608821503106161509013779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-50023207193425168784473022315400000000000000)
      constant := (1216583942174499122685638829841184397911973683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree118.table
  base := (2195161422002365305084518641958362004589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5647216048040905808924616543960000000000000)
      constant := (139497010820424866533254941852778146933510585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (534686863773018435721/100000000000000000000)
  centralHi := (267343431886509217861/50000000000000000000)
  directionLo := (536966988674719025937/100000000000000000000)
  directionHi := (268483494337359512969/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree119.table
  base := (5788072321094706312713602504249909595603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-50464842113181896981338736109600000000000000)
      constant := (1238756106326043600836556398673204251026290662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree119.table
  base := (723508988272750276643619958889600365553/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5697041526167305913186389382280000000000000)
      constant := (142035662989145344437250064107681741694873744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536966988674719025937/100000000000000000000)
  centralHi := (268483494337359512969/50000000000000000000)
  directionLo := (134809368081692788671/25000000000000000000)
  directionHi := (107847494465354230937/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree120.table
  base := (12185399973017384995596123404983109544097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5656275225882069464244938878200000000000000)
      constant := (140125352696069539538923631400962415760246841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree120.table
  base := (12185399243653609114837683531592078944577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-638540778254856224160906913400000000000000)
      constant := (16066352562988750507454050364037065342057809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134809368081692788671/25000000000000000000)
  centralHi := (107847494465354230937/20000000000000000000)
  directionLo := (135374609001359340733/25000000000000000000)
  directionHi := (541498436005437362933/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree121.table
  base := (200055844011633787811530176817661512039/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-51348111952695353375070163698000000000000000)
      constant := (1283700145949198338006647201397086873732972992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree121.table
  base := (6401786687862211631743081782057085064677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5796692482420106121709935058920000000000000)
      constant := (147181541049377195671648083860029468029791162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135374609001359340733/25000000000000000000)
  centralHi := (541498436005437362933/100000000000000000000)
  directionLo := (108749999693113415519/20000000000000000000)
  directionHi := (135937499616391769399/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree122.table
  base := (13430666745043426723599647351083102118893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-51789746872452081571935877492200000000000000)
      constant := (1306472021340754054778787399662441431617715661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree122.table
  base := (13430666181704610677373524971044996596617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5846517960546506225971707897240000000000000)
      constant := (149788766932469276813119871185049884479282401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108749999693113415519/20000000000000000000)
  centralHi := (135937499616391769399/25000000000000000000)
  directionLo := (545992276013382496487/100000000000000000000)
  directionHi := (68249034501672812061/12500000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree123.table
  base := (2813335626184293753793338582161427740647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5803486865800978863200176809600000000000000)
      constant := (147715977822458257898248666963853492221594955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree123.table
  base := (14066677635883303783704403970266874208077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-655149270963656258914831192840000000000000)
      constant := (16935427856915692805873791621414536861537309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545992276013382496487/100000000000000000000)
  centralHi := (68249034501672812061/12500000000000000000)
  directionLo := (548225382576585112663/100000000000000000000)
  directionHi := (68528172822073139083/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree124.table
  base := (14711608148591990879225546281516236473137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-52673016711965537965667305080600000000000000)
      constant := (1352615483097800854222026791033647857623509649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree124.table
  base := (58846430854408404143511767241834779917/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5946168916799306434495253573880000000000000)
      constant := (155071792384920335554250912694120180331825250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (548225382576585112663/100000000000000000000)
  centralHi := (68528172822073139083/12500000000000000000)
  directionLo := (550449429771902450479/100000000000000000000)
  directionHi := (6880617872148780631/1250000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree125.table
  base := (614618270934414691745959922688105928111/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-53114651631722266162533018874800000000000000)
      constant := (1375987069393779154519632397401038046575221175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree125.table
  base := (3841364097789894285650573870634291229329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-5995994394925706538757026412200000000000000)
      constant := (157747591946880259647712583508828186232349348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550449429771902450479/100000000000000000000)
  centralHi := (6880617872148780631/1250000000000000000)
  directionLo := (110532905394037666001/20000000000000000000)
  directionHi := (276332263485094165003/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree126.table
  base := (16028223981523823214517910853033316094187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-1983566168573296087385138247000000000000000)
      constant := (51835502194719277817799835909504699120803537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree126.table
  base := (1001763977857947089283367892012176063151/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-671757763672456293668755472280000000000000)
      constant := (17827361043847581666213507721507311889177072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110532905394037666001/20000000000000000000)
  centralHi := (276332263485094165003/50000000000000000000)
  directionLo := (138717695339796023849/25000000000000000000)
  directionHi := (554870781359184095397/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree127.table
  base := (3339981950056607826865486238473751761153/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-53997921471235722556264446463200000000000000)
      constant := (1423329952657330230943082124304391780875538405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree127.table
  base := (16699909455274888437581989408317548683979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6095645351178506747280572088840000000000000)
      constant := (163167764724793680556095989758352584948648787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138717695339796023849/25000000000000000000)
  centralHi := (554870781359184095397/100000000000000000000)
  directionLo := (557068298004042711107/100000000000000000000)
  directionHi := (139267074501010677777/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree128.table
  base := (4345128514416025481648152800932869795977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-54439556390992450753130160257400000000000000)
      constant := (1447301249563250265731922288411538246836241316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree128.table
  base := (3476102759701186838157666974471044994421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6145470829304906851542344927160000000000000)
      constant := (165912137934118178587455228990350349420732065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (557068298004042711107/100000000000000000000)
  centralHi := (139267074501010677777/25000000000000000000)
  directionLo := (139814294976428106067/25000000000000000000)
  directionHi := (559257179905712424269/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree129.table
  base := (2258754610306188954642161286593170934413/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6097910145638797661110652672400000000000000)
      constant := (163496938882884900890023943193290041223721512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree129.table
  base := (18070036654798564866382440395817148469933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-688366256381256328422679751720000000000000)
      constant := (18742152113271845004363155933608891523988861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139814294976428106067/25000000000000000000)
  centralHi := (559257179905712424269/100000000000000000000)
  directionLo := (70179691007158973791/12500000000000000000)
  directionHi := (561437528057271790329/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree130.table
  base := (18768478204117116509133413259865939632477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-55322826230505907146861587845800000000000000)
      constant := (1495843553777212754808809493278835398873920829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree130.table
  base := (18768478004154825178290151140620836957171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6245121785557707060065890603800000000000000)
      constant := (171469457977719272752766167304514988054447163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70179691007158973791/12500000000000000000)
  centralHi := (561437528057271790329/100000000000000000000)
  directionLo := (563609441498303242333/100000000000000000000)
  directionHi := (281804720749151621167/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree131.table
  base := (4868959500696497888558549875467682479239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-55764461150262635343727301640000000000000000)
      constant := (1520414561029620172418750785138575995095648412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree131.table
  base := (9737918913577484044081184007740716648737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6294947263684107164327663442120000000000000)
      constant := (174282404805964960431081108535488659294513522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563609441498303242333/100000000000000000000)
  centralHi := (281804720749151621167/50000000000000000000)
  directionLo := (70721627170923504163/12500000000000000000)
  directionHi := (113154603473477606661/20000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree132.table
  base := (20192116259168400596273056267236220613917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6245121785557707060065890603800000000000000)
      constant := (171687274630736349791717551788887141753929301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree132.table
  base := (10096058052458479021446224504064429373137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-704974749090056363176604031160000000000000)
      constant := (19679801055699412959398656763058190598686658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70721627170923504163/12500000000000000000)
  centralHi := (113154603473477606661/20000000000000000000)
  directionLo := (141982087738200319733/25000000000000000000)
  directionHi := (567928350952801278933/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree133.table
  base := (10458656477263545238735910188023495978977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-56647730989776091737458729228400000000000000)
      constant := (1570156285692432484330670505464316707926102658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree133.table
  base := (10458656409530204364359206881360631977661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6394598219936907372851209118760000000000000)
      constant := (179976872060896342257280991306176353385164266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141982087738200319733/25000000000000000000)
  centralHi := (567928350952801278933/100000000000000000000)
  directionLo := (570075535741481958171/100000000000000000000)
  directionHi := (142518883935370489543/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree134.table
  base := (5412857017659315262301502464186500789839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-57089365909532819934324443022600000000000000)
      constant := (1595327003051940631229732491556739246350433212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree134.table
  base := (270642849395930064423688798614871191651/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6444423698063307477112981957080000000000000)
      constant := (182858392482029467305423340617766023385808240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570075535741481958171/100000000000000000000)
  centralHi := (142518883935370489543/25000000000000000000)
  directionLo := (114442932693269815513/20000000000000000000)
  directionHi := (286107331733174538783/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree135.table
  base := (174956731169942479937944248134375304947/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-2130777808492205486340376178400000000000000)
      constant := (60025837915952406233840158909321201990694016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree135.table
  base := (22394461485288730263828053388383809909537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-721583241798856397930528310600000000000000)
      constant := (20640307862446794285518000611602524768462129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114442932693269815513/20000000000000000000)
  centralHi := (286107331733174538783/50000000000000000000)
  directionLo := (114869164830406351471/20000000000000000000)
  directionHi := (143586456038007939339/25000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree136.table
  base := (4629282698915028672092256602213107165659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-57972635749046276328055870611000000000000000)
      constant := (1646268147704936044564845515018237242835562215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree136.table
  base := (11573206701424038802091980348551990699507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6544074654316107685636527633720000000000000)
      constant := (188690006898261924162483990826976909154049142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114869164830406351471/20000000000000000000)
  centralHi := (143586456038007939339/25000000000000000000)
  directionLo := (576469106159077740841/100000000000000000000)
  directionHi := (288234553079538870421/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree137.table
  base := (23907283768227737567179731729651839755913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-58414270668803004524921584405200000000000000)
      constant := (1672038574951364174158227324054230583343892201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree137.table
  base := (23907283687688884953031608659809420186029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6593900132442507789898300472040000000000000)
      constant := (191640100888202269063933820360630841288462437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576469106159077740841/100000000000000000000)
  centralHi := (288234553079538870421/50000000000000000000)
  directionLo := (723230745283377189/125000000000000000)
  directionHi := (578584596226701751201/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree138.table
  base := (12338536197115015141243839325189969214199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6539545065395525857976366466600000000000000)
      constant := (188667656160811762264546559789508130579544894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree138.table
  base := (2467707232351847036475086905467313649181/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-738191734507656432684452590040000000000000)
      constant := (21623672525483266992925734943049443320360770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (723230745283377189/125000000000000000)
  centralHi := (578584596226701751201/100000000000000000000)
  directionLo := (580692379514132210817/100000000000000000000)
  directionHi := (290346189757066105409/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree139.table
  base := (25455779356476345043723831519901629342173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-59297540508316460918653011993600000000000000)
      constant := (1724179139170583586743836057739404543604172221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree139.table
  base := (25455779294396192596206315385883764754919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6693551088695307998421846148680000000000000)
      constant := (197608862419264407669477652953560216007502607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580692379514132210817/100000000000000000000)
  centralHi := (290346189757066105409/50000000000000000000)
  directionLo := (582792539640612086907/100000000000000000000)
  directionHi := (145698134910153021727/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree140.table
  base := (26243404639215933023739764083876083939049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-59739175428073189115518725787800000000000000)
      constant := (1750549276099508572111995000003497367584070473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree140.table
  base := (13121702292358196597157218066385153595063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6743376566821708102683618987000000000000000)
      constant := (200627529955559617520050158496313857000089278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582792539640612086907/100000000000000000000)
  centralHi := (145698134910153021727/25000000000000000000)
  directionLo := (58488515872410702407/10000000000000000000)
  directionHi := (584885158724107024071/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree141.table
  base := (27039948227035083769436548025516970738999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6686756705314435256931604398000000000000000)
      constant := (197457701801428459687942071178404096523066847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree141.table
  base := (27039948179192908288149971316587328019807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-754800227216456467438376869480000000000000)
      constant := (22629895037321805490644174037661984576336719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58488515872410702407/10000000000000000000)
  centralHi := (584885158724107024071/100000000000000000000)
  directionLo := (117394063483754292111/20000000000000000000)
  directionHi := (146742579354692865139/25000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree142.table
  base := (217542266444069595878485568209488602951/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-60622445267586645509250153376200000000000000)
      constant := (1803889259489843373817764201390331623201731456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree142.table
  base := (3480676257855620616926460788063595671487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6843027523074508311207164663640000000000000)
      constant := (206733438557982245096547787582669841101900088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117394063483754292111/20000000000000000000)
  centralHi := (146742579354692865139/25000000000000000000)
  directionLo := (589048094951221091947/100000000000000000000)
  directionHi := (147262023737805272987/25000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree143.table
  base := (28659790257846598265124300608104470495979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-61064080187343373706115867170400000000000000)
      constant := (1830859105910108847006305512113859855872963083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree143.table
  base := (7164947555246075058413471435309030513693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6892853001200908415468937501960000000000000)
      constant := (209820679619570300338226630838089126674380116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589048094951221091947/100000000000000000000)
  centralHi := (147262023737805272987/25000000000000000000)
  directionLo := (147779642288914458979/25000000000000000000)
  directionHi := (591118569155657835917/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree144.table
  base := (29483088671557990062957176788677904642151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-2277989448411114885295614109800000000000000)
      constant := (68815883535322003457908409248222573136749701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree144.table
  base := (2948308863920336176631318786141936703771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-771408719925256502192301148920000000000000)
      constant := (23658975390939562180122210966124129239641070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147779642288914458979/25000000000000000000)
  centralHi := (591118569155657835917/100000000000000000000)
  directionLo := (9268465882935802459/1562500000000000000)
  directionHi := (593181816507891357377/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree145.table
  base := (30315305331761282610038007955740343604721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-61947350026856830099847294758800000000000000)
      constant := (1885398508101026708835445187297554453143700817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree145.table
  base := (30315305303364465699782361779908354903311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6992503957453708623992483178600000000000000)
      constant := (216063735252476457318625684828325978300206583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9268465882935802459/1562500000000000000)
  centralHi := (593181816507891357377/100000000000000000000)
  directionLo := (595237912158299227943/100000000000000000000)
  directionHi := (74404739019787403493/12500000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree146.table
  base := (7789110056127944505188803624748844191741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-62388984946613558296713008553000000000000000)
      constant := (1912968063832904844433572779777116633808109428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree146.table
  base := (1557822009979490215899373933828522471109/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7042329435580108728254256016920000000000000)
      constant := (219219549819508188850244678128235278761593540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595237912158299227943/100000000000000000000)
  centralHi := (74404739019787403493/12500000000000000000)
  directionLo := (119457385992753182133/20000000000000000000)
  directionHi := (298643464981882955333/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree147.table
  base := (16003246668061764595751002403299637937547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-6981179985152254054842080260800000000000000)
      constant := (215637502514498105666249252787909689208889382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree147.table
  base := (16003246657126104134448516488058666115561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-788017212634056536946225428360000000000000)
      constant := (24710913579718477478344006471313994647929074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119457385992753182133/20000000000000000000)
  centralHi := (298643464981882955333/50000000000000000000)
  directionLo := (149832235629659743673/25000000000000000000)
  directionHi := (599328942518638974693/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree148.table
  base := (32865464653159793280584386730925354351369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-63272254786127014690444436141400000000000000)
      constant := (1968706884475258633630444046052484212941835113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree148.table
  base := (32865464633966580558911880254848878692311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7141980391832908936777801693560000000000000)
      constant := (225599752444302862843159156072271878439923583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149832235629659743673/25000000000000000000)
  centralHi := (599328942518638974693/100000000000000000000)
  directionLo := (601364021184739249133/100000000000000000000)
  directionHi := (300682010592369624567/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree149.table
  base := (3373335416242420228390038397620785092801/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-63713889705883742887310149935600000000000000)
      constant := (1996876149349060493594526671301738210727869770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree149.table
  base := (16866677072790964794409232017089525436969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7191805869959309041039574531880000000000000)
      constant := (228824140498005783749754297478349394783712514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601364021184739249133/100000000000000000000)
  centralHi := (300682010592369624567/50000000000000000000)
  directionLo := (603392236120460015831/100000000000000000000)
  directionHi := (75424029515057501979/12500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree150.table
  base := (17305080925476286398255894084662362296699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7128391625071163453797318192200000000000000)
      constant := (225027257470448538926654581989906682862789894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree150.table
  base := (6922032367234787494577145905319579591923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-804625705342856571700149707800000000000000)
      constant := (25785709597399737709818292341952164265313455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603392236120460015831/100000000000000000000)
  centralHi := (75424029515057501979/12500000000000000000)
  directionLo := (302706828154494406017/50000000000000000000)
  directionHi := (121082731261797762407/20000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree151.table
  base := (7099177541201057308981471516751608101809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-64597159545397199281041577524000000000000000)
      constant := (2053814388112645249503912766017334821780954965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree151.table
  base := (277311622601859435074426624424968783547/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7291456826212109249563120208520000000000000)
      constant := (235341490078134626491187335342658588656984448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302706828154494406017/50000000000000000000)
  centralHi := (121082731261797762407/20000000000000000000)
  directionLo := (607428349585683961597/100000000000000000000)
  directionHi := (303714174792841980799/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree152.table
  base := (18195265857530090787648083249659888259403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-65038794465153927477907291318200000000000000)
      constant := (2082583361967642674076221150909563332266395862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree152.table
  base := (9097632925920685731195205196031974889881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7341282304338509353824893046840000000000000)
      constant := (238634451600705561269186487670851568632607172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607428349585683961597/100000000000000000000)
  centralHi := (303714174792841980799/50000000000000000000)
  directionLo := (60943638266463657297/10000000000000000000)
  directionHi := (609436382664636572971/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree153.table
  base := (9323523466451475310303064115809999208583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-2425201088330024284250852041200000000000000)
      constant := (78205638473410236516838250659125239838550932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree153.table
  base := (37294093855823809916679291924565433276307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-821234198051656606454073987240000000000000)
      constant := (26883363438047882303697868823037612365697219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60943638266463657297/10000000000000000000)
  centralHi := (609436382664636572971/100000000000000000000)
  directionLo := (305718910582223714927/50000000000000000000)
  directionHi := (122287564232889485971/20000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree154.table
  base := (9551643536533913620337109150702546493291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-65922064304667383871638718906600000000000000)
      constant := (2140721018539275333847727614846069626085046828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree154.table
  base := (19103287068689076650398980343346559108747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7440933260591309562348438723480000000000000)
      constant := (245288948101462057412713449270984047087276582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305718910582223714927/50000000000000000000)
  centralHi := (122287564232889485971/20000000000000000000)
  directionLo := (613432729633246952313/100000000000000000000)
  directionHi := (306716364816623476157/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree155.table
  base := (39127972544141346431318607757819096640241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-66363699224424112068504432700800000000000000)
      constant := (2170089701222842071127246033515016896073611857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree155.table
  base := (39127972536458524992070022052102075945529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7490758738717709666610211561800000000000000)
      constant := (248650483075980162350469156093971617619665937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613432729633246952313/100000000000000000000)
  centralHi := (306716364816623476157/50000000000000000000)
  directionLo := (615421171572985218639/100000000000000000000)
  directionHi := (7692764644662315233/1250000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree156.table
  base := (40058289048108043271696211696491444296859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7422814904908982251707794055000000000000000)
      constant := (244406476312960570435981961457563190977419427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree156.table
  base := (40058289041368299599694084662240657037957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-837842690760456641207998266680000000000000)
      constant := (28003875096021741317972814110938091169645269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615421171572985218639/100000000000000000000)
  centralHi := (7692764644662315233/1250000000000000000)
  directionLo := (617403209463017908243/100000000000000000000)
  directionHi := (154350802365754477061/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree157.table
  base := (8199504729301747893432221687639819348349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-67246969063937568462235860289200000000000000)
      constant := (2229426775304811835615366640901900156213382865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree157.table
  base := (40997523640596549834395599740300613517213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7590409694970509875133757238440000000000000)
      constant := (255442126464347414071312956021545993868133589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617403209463017908243/100000000000000000000)
  centralHi := (154350802365754477061/25000000000000000000)
  directionLo := (61937890478301294997/10000000000000000000)
  directionHi := (619378904783012949971/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree158.table
  base := (20972838163999699637306095994115351027399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-67688603983694296659101574083400000000000000)
      constant := (2259395166671721438983582773911793676729456846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree158.table
  base := (20972838161406679447215027695167018150237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7640235173096909979395530076760000000000000)
      constant := (258872234874701911708475132843201107553972522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61937890478301294997/10000000000000000000)
  centralHi := (619378904783012949971/100000000000000000000)
  directionLo := (621348318035201635763/100000000000000000000)
  directionHi := (155337079508800408941/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree159.table
  base := (42902747081414247658690725205637079050557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7570026544827891650663031986400000000000000)
      constant := (254395940100222074644977452344962473094735221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree159.table
  base := (10725686769216337366105813074198978556437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-854451183469256675961922546120000000000000)
      constant := (29147244565950299782665511663125530541837716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621348318035201635763/100000000000000000000)
  centralHi := (155337079508800408941/25000000000000000000)
  directionLo := (623311508765996983607/100000000000000000000)
  directionHi := (77913938595749622951/12500000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree160.table
  base := (43868735895761288609741304368433279660557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-68571873823207753052833001671800000000000000)
      constant := (2319931657980507555573714041555332626092586989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree160.table
  base := (43868735891771411278012957605161182389399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7739886129349710187919075753400000000000000)
      constant := (265801025119219663207102950769589660905578047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623311508765996983607/100000000000000000000)
  centralHi := (77913938595749622951/12500000000000000000)
  directionLo := (625268535587001203719/100000000000000000000)
  directionHi := (15631713389675030093/2500000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree161.table
  base := (11210910690054507840719170138884369797959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-69013508742964481249698715466000000000000000)
      constant := (2350499757892345520507083943499475108847158172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree161.table
  base := (448436427567186112236650394879823125801/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7789711607476110292180848591720000000000000)
      constant := (269299706950048428431750448077981293824755300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625268535587001203719/100000000000000000000)
  centralHi := (15631713389675030093/2500000000000000000)
  directionLo := (627219456195423235471/100000000000000000000)
  directionHi := (39201216012213952217/6250000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree162.table
  base := (143210836450398147537610198611670576011/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1672)
      previous := (1235)
      next := (0)
      square := (19250752912472767555684960260000000000000)
      linear := (-2572412728248933683206089972600000000000000)
      constant := (88195102245290288259135554341342463800499520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree162.table
  base := (22913733830529135874925207344704016476879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-871059676178056710715846825560000000000000)
      constant := (30313471842712194005838683017239936560213886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627219456195423235471/100000000000000000000)
  centralHi := (39201216012213952217/6250000000000000000)
  directionLo := (314582163696963238651/50000000000000000000)
  directionHi := (629164327393926477303/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree163.table
  base := (46820210596993861538625502255318661841851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-69896778582477937643430143054400000000000000)
      constant := (2412235666157531964332641546822073797356228827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree163.table
  base := (46820210594302204883129336990511874812251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7889362563728910500704394268360000000000000)
      constant := (276365644020698923309559766829628316846274403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314582163696963238651/50000000000000000000)
  centralHi := (629164327393926477303/100000000000000000000)
  directionLo := (631103205109926025723/100000000000000000000)
  directionHi := (157775801277481506431/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree164.table
  base := (4782187154847960736448616038970125259413/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-70338413502234665840295856848600000000000000)
      constant := (2443403474482192931846100659980618624822117010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree164.table
  base := (47821871546119090538584876535791413487179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7939188041855310604966167106680000000000000)
      constant := (279932899257335268229793016833496086263538387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631103205109926025723/100000000000000000000)
  centralHi := (157775801277481506431/25000000000000000000)
  directionLo := (39564759025897123149/6250000000000000000)
  directionHi := (126607228882870794077/20000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree165.table
  base := (48832450508401028223088262172043783187007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-7864449824665710448573507849200000000000000)
      constant := (274974576175866427295847434114822698827612071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree165.table
  base := (48832450506330989000856617598788662189717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-887668168886856745469771105000000000000000)
      constant := (31502556921417950670755305951179407257225189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39564759025897123149/6250000000000000000)
  centralHi := (126607228882870794077/20000000000000000000)
  directionLo := (126992639907982111637/20000000000000000000)
  directionHi := (317481599769955279093/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree166.table
  base := (49851947466725219447049699333052158804173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-71221683341748122234027284437000000000000000)
      constant := (2506338799445531396055235124893612822673346221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree166.table
  base := (12462986866227494626750862290767236838479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-8038838998108110813489712783320000000000000)
      constant := (287135983125443514700843987025469548945149148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126992639907982111637/20000000000000000000)
  centralHi := (317481599769955279093/50000000000000000000)
  directionLo := (636884423898818338719/100000000000000000000)
  directionHi := (3980527649367614617/625000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree167.table
  base := (50880362413566658116710939783168774873001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-71663318261504850430892998231200000000000000)
      constant := (2538106316056781217963554137873923403000122377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree167.table
  base := (50880362411974909788071797031208215731177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-8088664476234510917751485621640000000000000)
      constant := (290771811753869328383781820375854857006870081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636884423898818338719/100000000000000000000)
  centralHi := (3980527649367614617/625000000000000000)
  directionLo := (638799870100095734259/100000000000000000000)
  directionHi := (31939993505004786713/5000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree168.table
  base := (12979423834795998230866174923272003978499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (5016)
      previous := (3705)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-8011661464584619847528745780600000000000000)
      constant := (285563748378125941181736857349042466434841388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree168.table
  base := (207670781351153080962795933355572132999/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (551)
      previous := (418)
      next := (0)
      square := (6416917637490922518561653420000000000000)
      linear := (-904276661595656780223695384440000000000000)
      constant := (32714499797394350850810751544281181565245750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell023.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638799870100095734259/100000000000000000000)
  centralHi := (31939993505004786713/5000000000000000000)
  directionLo := (640709589966365838433/100000000000000000000)
  directionHi := (320354794983182919217/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree169.table
  base := (52963946233976946089971567520523840307849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (45144)
      previous := (33345)
      next := (0)
      square := (519770328636764724003493927020000000000000)
      linear := (-72546588101018306824624425819600000000000000)
      constant := (2602241057471368571572071490002261328103908073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree169.table
  base := (52963946232753151117397071892318934829567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4959)
      previous := (3762)
      next := (0)
      square := (57752258737418302667054880780000000000000)
      linear := (-8188315432487311126275031298280000000000000)
      constant := (298112042392014675483023163355844797028923751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell023.Kernel169
