import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell095.Parameters
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch000_049
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch050_099
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch100_149
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch150_199
import ForestUnimodality.BinomialMassData.Q107_207.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_207.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_207.Batch100_149
import ForestUnimodality.BinomialMassData.Q107_207.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree000.table
  base := (739312481093240489349227571/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (358474943618066338446581655000000000000)
      linear := (-14665490238395606850674291000000000000)
      constant := (369656240546620244674613785500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree000.table
  base := (739312481093240489349227571/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (358474943618066338446581655000000000000)
      linear := (-14665490238395606850674291000000000000)
      constant := (369656240546620244674613785500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree001.table
  base := (6372121269492340842383075237072406491021/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-6479393268048984186285128531719158000000000000)
      constant := (3434828036013358743095298662688107594715271012576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree001.table
  base := (101860126097842280371683668211372940327421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-5502708214539372006150405616083000000000000)
      constant := (2911212697301887069699185832205897413393108286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49971403056949760723/100000000000000000000)
  directionHi := (12492850764237440181/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree002.table
  base := (29878742813850526958205414509699160316579/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-4237290419670851596851398608159921000000000000)
      constant := (672967562513713770938483866661122519045809268876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree002.table
  base := (238649094380533859644304160100750114477581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-21591898464007479119305260667626000000000000)
      constant := (3420002595306840727051443534195745885083289423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49971403056949760723/100000000000000000000)
  centralHi := (12492850764237440181/25000000000000000000)
  directionLo := (70670235933950693029/100000000000000000000)
  directionHi := (7067023593395069303/10000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree003.table
  base := (150451916572667883348688140821974251432369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-12629566166650750263215508744826912000000000000)
      constant := (854269249421570781210678330338280445392935439409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree003.table
  base := (3003075596197738213603744689301285877311/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-1787687805496456345906095005727000000000000)
      constant := (120551175927116369049479717767544517182313925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70670235933950693029/100000000000000000000)
  centralHi := (7067023593395069303/10000000000000000000)
  directionLo := (2704781531879365517/3125000000000000000)
  directionHi := (17310601804027939309/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree004.table
  base := (50936428191373349113370066087075984090707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-25176827240939695999092330410000973000000000000)
      constant := (883843979245389688066839746639976627851458863481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree004.table
  base := (20331359357887495975586218627439599310793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-42764862533864949333314159538546000000000000)
      constant := (1496608147106797365980850438861902984780282095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2704781531879365517/3125000000000000000)
  centralHi := (17310601804027939309/20000000000000000000)
  directionLo := (49971403056949760723/50000000000000000000)
  directionHi := (99942806113899521447/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree005.table
  base := (73614134269081947043878702277738285439559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-20939536821268844402240931801841052000000000000)
      constant := (440375708499407090233551693322661796250760876999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree005.table
  base := (18364787183372595649260160561226676763619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-26675672284396842220159304487003000000000000)
      constant := (559351384164732287050949332778391248429540354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49971403056949760723/50000000000000000000)
  centralHi := (99942806113899521447/100000000000000000000)
  directionLo := (55869727083190229807/50000000000000000000)
  directionHi := (22347890833276091923/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree006.table
  base := (874563635521949618280681874968477035933/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-12547261074288945735876821665174061000000000000)
      constant := (176624907839960492276287999782049553614680998816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree006.table
  base := (27929070997896408226736179255890516133569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-1184033825994859621246723303879000000000000)
      constant := (16622619574197546125971962165620083034658001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55869727083190229807/50000000000000000000)
  centralHi := (22347890833276091923/20000000000000000000)
  directionLo := (122404439220482389111/100000000000000000000)
  directionHi := (15300554902560298639/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree007.table
  base := (44109412416800878334199989555529136428031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-87748522427660815623799064576565576000000000000)
      constant := (902112491183019762489051979988017310975224654973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree007.table
  base := (44022148822329492905797290544252830498091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-74524308638651154654327507844926000000000000)
      constant := (764354073927805749845382600267675178004233753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122404439220482389111/100000000000000000000)
  centralHi := (15300554902560298639/12500000000000000000)
  directionLo := (66105952576830959763/50000000000000000000)
  directionHi := (132211905153661919527/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree008.table
  base := (7114035837454887838309711656229224427339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-33404492803195985610779066387362262000000000000)
      constant := (268955429391879147532516374048632157956796347895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree008.table
  base := (1775017619336799515149931943996609289767/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-42555395336789944880665978640193000000000000)
      constant := (341947801180958158394557824404019704857420610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66105952576830959763/50000000000000000000)
  centralHi := (132211905153661919527/100000000000000000000)
  directionLo := (141340471867901386059/100000000000000000000)
  directionHi := (7067023593395069303/5000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree009.table
  base := (2907245833406449424237546319614567110123/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-18779739065252516340145888957934666000000000000)
      constant := (125404650632104681370569974695211338086575029015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree009.table
  base := (14507234634990083332467062928852317844083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-1772171716824233793858081605849000000000000)
      constant := (11814598522869687180209499087608876139519907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141340471867901386059/100000000000000000000)
  centralHi := (7067023593395069303/5000000000000000000)
  directionLo := (14991420917084928217/10000000000000000000)
  directionHi := (149914209170849282171/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree010.table
  base := (11959976712844297234482464872009300535601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-62571695186721119624706734166564603000000000000)
      constant := (363537077501188390840762910455816294309537131283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree010.table
  base := (23870483198053558523822887009574348521793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-106283754743437359975340856151306000000000000)
      constant := (616719593105283238961660418839810419936769419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14991420917084928217/10000000000000000000)
  centralHi := (149914209170849282171/100000000000000000000)
  directionLo := (158023451534262087543/100000000000000000000)
  directionHi := (19752931441782760943/12500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree011.table
  base := (1971383097249918364321382731070972686323/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-22934724392561563409658600486441736000000000000)
      constant := (120681681422766961090977426589445077961235870015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree011.table
  base := (3934180299309631973571670073182422740767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-116870236778366095082345305586766000000000000)
      constant := (614412033104307160613524785692618720031875305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158023451534262087543/100000000000000000000)
  centralHi := (19752931441782760943/12500000000000000000)
  directionLo := (82868197093760593653/50000000000000000000)
  directionHi := (165736394187521187307/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree012.table
  base := (16210587354585278732326465402804686300489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-50024434112432173888829912501390542000000000000)
      constant := (246458653279411105157160992860249715072838646729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree012.table
  base := (808648816389846947034381638170607769547/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-7080928822960823899408319723457000000000000)
      constant := (34866581825924258783939878948211545302710890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82868197093760593653/50000000000000000000)
  centralHi := (165736394187521187307/100000000000000000000)
  directionLo := (2704781531879365517/1562500000000000000)
  directionHi := (173106018040279393089/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree013.table
  base := (1325111799623080752977934621453452697033/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-81269129159611831437513936044846418000000000000)
      constant := (385126503711502782963237859068251175874501274695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree013.table
  base := (826126126347266843983427765159022240257/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-69021600424111782648177102228843000000000000)
      constant := (327006173916091008944130044336704517260725848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2704781531879365517/1562500000000000000)
  centralHi := (173106018040279393089/100000000000000000000)
  directionLo := (180174456028710303367/100000000000000000000)
  directionHi := (22521807003588787921/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree014.table
  base := (10724663841528005733454084729568497516177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-58334404767050268027855335558404682000000000000)
      constant := (271618812776343798223406574963007556588885428497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree014.table
  base := (10695493160283677099053851799574209083051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-148629682883152300403358653893146000000000000)
      constant := (692074909198184077262706970817082428333217433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180174456028710303367/100000000000000000000)
  centralHi := (22521807003588787921/12500000000000000000)
  directionLo := (186975869375493987763/100000000000000000000)
  directionHi := (46743967343873496941/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree015.table
  base := (8549969047791840672958732385346017560687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-62489390094359315097368047086911752000000000000)
      constant := (290606063314097858264405451175961483759402714607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree015.table
  base := (2131067642793864368818300516719772210549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-2948447498482982139080798209789000000000000)
      constant := (13715321489323843118739259241649518998760842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186975869375493987763/100000000000000000000)
  centralHi := (46743967343873496941/25000000000000000000)
  directionLo := (19353841182618482561/10000000000000000000)
  directionHi := (193538411826184825611/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree016.table
  base := (6665033687536193692567872993354318419583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-199933126265005086500642275846256466000000000000)
      constant := (940094401537670836812361781727267671047896046589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree016.table
  base := (1660605767977262203227319621662077378109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-84901323476504885308683776382033000000000000)
      constant := (399392597781489610434107339037086902383061694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19353841182618482561/10000000000000000000)
  centralHi := (193538411826184825611/100000000000000000000)
  directionLo := (199885612227799042893/100000000000000000000)
  directionHi := (99942806113899521447/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree017.table
  base := (1004247872528984538022198533593669721611/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-70799360748977409236393470143925892000000000000)
      constant := (339622170093931174066292629783527401792530556855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree017.table
  base := (156293100685343234988962895592085189817/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-90194564493969252862186001099763000000000000)
      constant := (432927334365616988505276014668054044258499376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199885612227799042893/100000000000000000000)
  centralHi := (99942806113899521447/50000000000000000000)
  directionLo := (51509343266029279517/25000000000000000000)
  directionHi := (206037373064117118069/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree018.table
  base := (1789881508325100073243793190170968920123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-37477173038143228152953090836216481000000000000)
      constant := (184580145407405502146749474698040833105726415803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree018.table
  base := (712470097516048932952697298886450471321/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-7073170778624712623384313023518000000000000)
      constant := (34862287529702647852497229020918661496644045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51509343266029279517/25000000000000000000)
  centralHi := (206037373064117118069/100000000000000000000)
  directionLo := (212010707801852079089/100000000000000000000)
  directionHi := (21201070780185207909/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree019.table
  base := (1154618491877236179789725052882047051711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-118663997105393255063128339801410048000000000000)
      constant := (602704683426819557254959226093838926941332372413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree019.table
  base := (229399777777424220172405526616880591719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-100781046528897987969190450535223000000000000)
      constant := (512309431518629566127085620162716527457612385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212010707801852079089/100000000000000000000)
  centralHi := (21201070780185207909/10000000000000000000)
  directionLo := (108910147996091748411/50000000000000000000)
  directionHi := (217820295992183496823/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree020.table
  base := (1184124508584113654015614883803093666523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-83264316730904550444931604729447102000000000000)
      constant := (437407348120562873251798621251014793954607386203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree020.table
  base := (585404951806433176218793164555842606551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-106074287546362355522692675252953000000000000)
      constant := (557750795813018314880158704324411099949367933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108910147996091748411/50000000000000000000)
  centralHi := (217820295992183496823/100000000000000000000)
  directionLo := (55869727083190229807/25000000000000000000)
  directionHi := (223478908332760919229/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree021.table
  base := (45883138248800736740937202549686398103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-43709651029106798757222158128977086000000000000)
      constant := (237927856614508841625413489154651708381328261166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree021.table
  base := (171917576426914371517529882330553862727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (234876)
      previous := (117438)
      next := (117438)
      square := (1137799471043742558229450172970000000000000)
      linear := (-24748339680850382905821088882374000000000000)
      constant := (134847985890915751302611955303142588980147749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55869727083190229807/25000000000000000000)
  centralHi := (223478908332760919229/100000000000000000000)
  directionLo := (228997737091619937497/100000000000000000000)
  directionHi := (114498868545809968749/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree022.table
  base := (-177422480233912589517838014342490233963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-137361431078283966875935541679691863000000000000)
      constant := (775577944835651441710461152477927389996431855742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree022.table
  base := (-179951981224464275794013186953270009241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-116660769581291090629697124688413000000000000)
      constant := (659382528845099895101148531744118888916021594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228997737091619937497/100000000000000000000)
  centralHi := (114498868545809968749/50000000000000000000)
  directionLo := (29298332054850732791/12500000000000000000)
  directionHi := (234386656438805862329/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree023.table
  base := (-754827767116212723512130231021100209899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (785066)
      previous := (392533)
      next := (392533)
      square := (3803060676844065784579784777895000000000000)
      linear := (-90481354170918423112920358520764000000000000)
      constant := (530167198301979348646622148939745397873181509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree023.table
  base := (-151845828542139910560896097282780670917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (1998)
      previous := (999)
      next := (999)
      square := (9678823477687791138057704685000000000000)
      linear := (-230536882039235270667673628367000000000000)
      constant := (1352268312007749938164983263642824609426205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29298332054850732791/12500000000000000000)
  centralHi := (234386656438805862329/100000000000000000000)
  directionLo := (239654430044685260961/100000000000000000000)
  directionHi := (119827215022342630481/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree024.table
  base := (-278499678279226413652288412506848082113/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-49942129020070369361491225421737691000000000000)
      constant := (303692611958646548148636780021122623842562495228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree024.table
  base := (-2235647143241415809249806129989882658389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-9425722341942209313829746231398000000000000)
      constant := (57380386839529303190467448530947352073712219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239654430044685260961/100000000000000000000)
  centralHi := (119827215022342630481/50000000000000000000)
  directionLo := (244808878440964778223/100000000000000000000)
  directionHi := (15300554902560298639/6250000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree025.table
  base := (-114972740175020586500107401725021579733/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-312117730102349357377485487115947356000000000000)
      constant := (1969209163507701542535194517518001174954805024025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree025.table
  base := (-1440479699559364468409189616097457217741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-132540492633684193290203798841603000000000000)
      constant := (837169934120954114114448370327730018559005297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244808878440964778223/100000000000000000000)
  centralHi := (15300554902560298639/6250000000000000000)
  directionLo := (7808031727648400113/3125000000000000000)
  directionHi := (249857015284748803617/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree026.table
  base := (-1728277642245983271606260149045066891883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-54097114347379416431003936950244761000000000000)
      constant := (353962923277337264096095245248285294346983010837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree026.table
  base := (-865578771382815351241688503421482648671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-137833733651148560843706023559333000000000000)
      constant := (902897511502084193909418807373779926658064214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7808031727648400113/3125000000000000000)
  centralHi := (249857015284748803617/100000000000000000000)
  directionLo := (1990665307101538827/781250000000000000)
  directionHi := (254805159308996969857/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree027.table
  base := (-1990637018015282826293262864825081483619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-56174607011033939965760292714498296000000000000)
      constant := (380958374556153477898053979553455734125811309341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree027.table
  base := (-498283187705236565389548700334725801927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-5300999061800478829526231417669000000000000)
      constant := (35991524754594967772888463553399720203122468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1990665307101538827/781250000000000000)
  centralHi := (254805159308996969857/100000000000000000000)
  directionLo := (8114344595638096551/3125000000000000000)
  directionHi := (259659027060419089633/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree028.table
  base := (-2226956324341934236513463007738216025499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-174756299024065390501549945436255493000000000000)
      constant := (1227517865794514394263973440031642051436358519983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree028.table
  base := (-22291175175002719927082453216774273023/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-148420215686077295950710472994793000000000000)
      constant := (1043752166473206156211390951065325305841249100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8114344595638096551/3125000000000000000)
  centralHi := (259659027060419089633/100000000000000000000)
  directionLo := (264423810307323839053/100000000000000000000)
  directionHi := (132211905153661919527/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree029.table
  base := (-4878978649535149248436428861552198405339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-120659184676685974070546008486010732000000000000)
      constant := (877186033839079253867878229257201583145294272421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree029.table
  base := (-2441359553710468787531609095397882248267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-153713456703541663504212697712523000000000000)
      constant := (1118808401744627578824930728569534047848002439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264423810307323839053/100000000000000000000)
  centralHi := (132211905153661919527/50000000000000000000)
  directionLo := (269104241105419423373/100000000000000000000)
  directionHi := (134552120552709711687/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree030.table
  base := (-5260211619709601111722691040535437085539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-124814170003995021140058720014517802000000000000)
      constant := (938418131909168783853823598874335160870584360221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree030.table
  base := (-328965406417985003500168657647128341277/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-17667410857889559006412769158917000000000000)
      constant := (132990360564325561909320731960522058579147208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269104241105419423373/100000000000000000000)
  centralHi := (134552120552709711687/50000000000000000000)
  directionLo := (136852323422369995151/50000000000000000000)
  directionHi := (273704646844739990303/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree031.table
  base := (-5600716609644150347247408094659827253689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-386907465993912204628714294629074616000000000000)
      constant := (3006072336090939106442546353769493181160328464213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree031.table
  base := (-5603512682706970546055660981487435892457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-328599877476940797222434294295966000000000000)
      constant := (2556089180469824368496683579369030953148036669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136852323422369995151/50000000000000000000)
  centralHi := (273704646844739990303/100000000000000000000)
  directionLo := (69557249275275023549/25000000000000000000)
  directionHi := (278228997101100094197/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree032.table
  base := (-18447105848072227860591371491216600049/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-66562070329306557639542071535765971000000000000)
      constant := (533994746706309364222219565977548328744384657760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree032.table
  base := (-2952744708210561805126370548833399389837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-169593179755934766164719371865713000000000000)
      constant := (1362184070924670706592130051055268556514958129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69557249275275023549/25000000000000000000)
  centralHi := (278228997101100094197/100000000000000000000)
  directionLo := (282680943735802772119/100000000000000000000)
  directionHi := (7067023593395069303/2500000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree033.table
  base := (-6169429215167476876555697819629782137409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-137279125985922162348596854600039012000000000000)
      constant := (1136302233423537988950509944370697420749936569151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree033.table
  base := (-1542878758283476847032634666271068373229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-6477274843459227174748948021609000000000000)
      constant := (53678385787758642050620397938027209661123718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282680943735802772119/100000000000000000000)
  centralHi := (7067023593395069303/2500000000000000000)
  directionLo := (287063855396049853167/100000000000000000000)
  directionHi := (17941490962253115823/6250000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree034.table
  base := (-6401568490375128643839377012467638318169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-424302333939693628254328698385638246000000000000)
      constant := (3620856928766521105827219261352491303405999040373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree034.table
  base := (-3201684401681841705434740307387146124619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-180179661790863501271723821301173000000000000)
      constant := (1539428919608943191697278850570931391902066823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287063855396049853167/100000000000000000000)
  centralHi := (17941490962253115823/6250000000000000000)
  directionLo := (291380847342999447687/100000000000000000000)
  directionHi := (36422605917874930961/12500000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree035.table
  base := (-330048952089251200733077384236201642609/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-72794548320270128243811138828526576000000000000)
      constant := (639965687345081929036558500616780559782138319510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree035.table
  base := (-6602532300213079099909603608496180808063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-370945805616655737650452092037806000000000000)
      constant := (3265022000577475723707000695935809049518436171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291380847342999447687/100000000000000000000)
  centralHi := (36422605917874930961/12500000000000000000)
  directionLo := (73908701839585707619/25000000000000000000)
  directionHi := (295634807358342830477/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree036.table
  base := (-3384450233850230477235757310563984726483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-74872040983924651778567494592780111000000000000)
      constant := (677616235951127511164783875464459982913436440237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree036.table
  base := (-1692560017250914399183808505486374088973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-7065412734288601347360306323579000000000000)
      constant := (64020512659387163061500182211319416213866566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73908701839585707619/25000000000000000000)
  centralHi := (295634807358342830477/100000000000000000000)
  directionLo := (14991420917084928217/5000000000000000000)
  directionHi := (299828418341698564341/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree037.table
  base := (-6906366581347487073463538229221291102597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-461697201885475051879943102142201876000000000000)
      constant := (4298549397896536058389049716561569608613074353649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree037.table
  base := (-6907521507215437309589311375570586825449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-392118769686513207864460990908726000000000000)
      constant := (3655100185421972525311651226397617308372111933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14991420917084928217/5000000000000000000)
  centralHi := (299828418341698564341/100000000000000000000)
  directionLo := (303964178101243916899/100000000000000000000)
  directionHi := (3039641781012439169/1000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree038.table
  base := (-876780016442546051329009205307227229057/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-79027026311233698848080206121287181000000000000)
      constant := (756389257497343314682897152346075753307792951292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree038.table
  base := (-7015235510925113632745634183738415868303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-402705251721441942971465440344186000000000000)
      constant := (3858987238410009443362512192714212206153028251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303964178101243916899/100000000000000000000)
  centralHi := (3039641781012439169/1000000000000000000)
  directionLo := (308044416752267821161/100000000000000000000)
  directionHi := (154022208376133910581/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree039.table
  base := (-886655194678590713636505645269524589891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-81104518974888222382836561885540716000000000000)
      constant := (797507287884640238669300175880996058682290942196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree039.table
  base := (-7094099162467965722073831775486417331563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (234876)
      previous := (117438)
      next := (117438)
      square := (1137799471043742558229450172970000000000000)
      linear := (-45921303750707853119829987753294000000000000)
      constant := (452084288942669196365589646961599055694809519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308044416752267821161/100000000000000000000)
  centralHi := (154022208376133910581/50000000000000000000)
  directionLo := (12482852482712434121/4000000000000000000)
  directionHi := (156035656033905426513/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree040.table
  base := (-3571986411461033049894745825824172067011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-249546034915628237752778752949382753000000000000)
      constant := (2519331904956375829897876191475153986004694437687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree040.table
  base := (-7144711504636317789663536785033675953437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-423878215791299413185474339215106000000000000)
      constant := (4284405715515809730373758893303604006357059329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12482852482712434121/4000000000000000000)
  centralHi := (156035656033905426513/50000000000000000000)
  directionLo := (316046903068524175087/100000000000000000000)
  directionHi := (19752931441782760943/6250000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree041.table
  base := (-3583468594642843489700020199834306528039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-85259504302197269452349273414047786000000000000)
      constant := (883197886608175472221360573618056225691294117721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree041.table
  base := (-7167573259505121891747598884309885769513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-434464697826228148292478788650566000000000000)
      constant := (4505921431691973792393694612797677901554045821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316046903068524175087/100000000000000000000)
  centralHi := (19752931441782760943/6250000000000000000)
  directionLo := (159986551046240480177/50000000000000000000)
  directionHi := (63994620418496192071/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree042.table
  base := (-7162555631500243505047930644756272548967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-174673993931703585974211258356602642000000000000)
      constant := (1855535722926213242243749882910821716695316812313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree042.table
  base := (-3581551598502849538087372356983170326231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-8241688515947349692583022927519000000000000)
      constant := (87653699402251590644883159602373902897423801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159986551046240480177/50000000000000000000)
  centralHi := (63994620418496192071/20000000000000000000)
  directionLo := (323851705547717274053/100000000000000000000)
  directionHi := (161925852773858637027/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree043.table
  base := (-222849389965217607412478430261980485873/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-268243468888518949565585954827664568000000000000)
      constant := (2920458712657442543638397320779521312802279925456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree043.table
  base := (-3565825866623983851527763163898684898937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-227818830948042809253243843760743000000000000)
      constant := (2483267859305674036863143947755399083588482829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323851705547717274053/100000000000000000000)
  centralHi := (161925852773858637027/50000000000000000000)
  directionLo := (327684403519065123221/100000000000000000000)
  directionHi := (163842201759532561611/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree044.table
  base := (-1768276689513687586497099544104772551091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-91491982293160840056618340706808391000000000000)
      constant := (1020352187007883927059599051767733405149793164698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree044.table
  base := (-1414702447228261508447966913404221744883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-466224143931014353613492136956946000000000000)
      constant := (5205625094187410657848720452860381504089180555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327684403519065123221/100000000000000000000)
  centralHi := (163842201759532561611/50000000000000000000)
  directionLo := (82868197093760593653/25000000000000000000)
  directionHi := (331472788375042374613/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree045.table
  base := (-6988581632238491062301189538200545797687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-187138949913630727182749392942123852000000000000)
      constant := (2136730032538764251612837582840878789195507128393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree045.table
  base := (-698893043189028481842679206178386086889/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-8829826406776723865194381229489000000000000)
      constant := (100936377495229515329696494852788168800178595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82868197093760593653/25000000000000000000)
  centralHi := (331472788375042374613/100000000000000000000)
  directionLo := (167609181249570689421/50000000000000000000)
  directionHi := (335218362499141378843/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree046.table
  base := (-6877812262174072220639665174299834474123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318270000000000000000000000000000000000000000
      center := (4710396)
      previous := (2355198)
      next := (2355198)
      square := (22818364061064394707478708667370000000000000)
      linear := (-1084842732935386243396571480929854000000000000)
      constant := (12675132068362277205874915185893423168192087279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree046.table
  base := (-1719528059260461306834240129135590881923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (1998)
      previous := (999)
      next := (999)
      square := (9678823477687791138057704685000000000000)
      linear := (-460677795842033859950379050877000000000000)
      constant := (5388800235510640414195635085308678092376158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167609181249570689421/50000000000000000000)
  centralHi := (335218362499141378843/100000000000000000000)
  directionLo := (169461272625994021673/50000000000000000000)
  directionHi := (338922545251988043347/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree047.table
  base := (-6740972357036779923987333009908233155941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-195448920568248821321774815999137992000000000000)
      constant := (2335658165679260858357509461529501896803321001499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree047.table
  base := (-3370615142086308253674736141866542256759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-248991795017900279467252742631663000000000000)
      constant := (2978990710879954937553782450044296176946711203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169461272625994021673/50000000000000000000)
  centralHi := (338922545251988043347/100000000000000000000)
  directionLo := (171293339627936213341/50000000000000000000)
  directionHi := (342586679255872426683/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree048.table
  base := (-1644551909353283327030841240078779676387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-99801952947778934195643763763822531000000000000)
      constant := (1219279423802754812478981130428240639545176515386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree048.table
  base := (-3289214681391329570120574020879467761551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-28253892892818294113417218594377000000000000)
      constant := (345580813026828967478230073988720284662418563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171293339627936213341/50000000000000000000)
  centralHi := (342586679255872426683/100000000000000000000)
  directionLo := (2704781531879365517/781250000000000000)
  directionHi := (346212036080558786177/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree049.table
  base := (-6389640393956149323642596679624482311363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-611276673668600746382400717168456396000000000000)
      constant := (7631248942555382962524503536902319568680936143671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree049.table
  base := (-6389830958677477970191534074833962319003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-519156554105658029148514384134246000000000000)
      constant := (6488768552157532151031294755804270516197680151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2704781531879365517/781250000000000000)
  centralHi := (346212036080558786177/100000000000000000000)
  directionLo := (349799821398648325063/100000000000000000000)
  directionHi := (43724977674831040633/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree050.table
  base := (-1543843323450734782869713874144118647681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-103956938275087981265156475292329601000000000000)
      constant := (1325614994616806034549034333273643987892223902718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree050.table
  base := (-3087768521792107731824568762284426550093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-264871518070293382127759416784853000000000000)
      constant := (3381460859160781654264370572303441535585021681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349799821398648325063/100000000000000000000)
  centralHi := (43724977674831040633/12500000000000000000)
  directionLo := (353351179669753465149/100000000000000000000)
  directionHi := (7067023593395069303/2000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree051.table
  base := (-5935492560797994090934829450682804089067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-212068861877485009599825662113166272000000000000)
      constant := (2760999388848865545256149190585511568020697656213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree051.table
  base := (-5935633240746281944631734374395604994033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-20012204376870944420834195666858000000000000)
      constant := (260848626296971453979353133475312724958156543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353351179669753465149/100000000000000000000)
  centralHi := (7067023593395069303/2000000000000000000)
  directionLo := (356867198405074100247/100000000000000000000)
  directionHi := (44608399800634262531/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree052.table
  base := (-177189707314837536071263478972939624933/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-324335770807191085004007560462510013000000000000)
      constant := (4309586159736212380072307027613493878716626709776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree052.table
  base := (-2835095735390942394228424279000842749007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-275458000105222117234763866220313000000000000)
      constant := (3664370550002670070915507469569546963015933019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356867198405074100247/100000000000000000000)
  centralHi := (44608399800634262531/12500000000000000000)
  directionLo := (72069782411484121347/20000000000000000000)
  directionHi := (22521807003588787921/6250000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree053.table
  base := (-5379168391792802596064759822734184957759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-220378832532103103738851085170180412000000000000)
      constant := (2987403800501408019759259405726387252313278292801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree053.table
  base := (-2689636082182957102248422922132984187107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-280751241122686484788266090938043000000000000)
      constant := (3810202712575783252416858325123468586855550719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72069782411484121347/20000000000000000000)
  centralHi := (22521807003588787921/6250000000000000000)
  directionLo := (45474663197015334351/12500000000000000000)
  directionHi := (363797305576122674809/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree054.table
  base := (-2531418506071861425832979233546370600147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-112266908929706075404181898349343741000000000000)
      constant := (1552019091830206598995168557584204151226308412333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree054.table
  base := (-2531463056819403504242259833385471287263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-10594240079264846383028456135399000000000000)
      constant := (146627873333199379396509782380465085689037873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45474663197015334351/12500000000000000000)
  centralHi := (363797305576122674809/100000000000000000000)
  directionLo := (183606658830723583667/50000000000000000000)
  directionHi := (73442663532289433467/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree055.table
  base := (-944223906317681942625876471635489652127/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-686066409560163593633629524681583656000000000000)
      constant := (9668881043320829920207954283869280498876439253295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree055.table
  base := (-944239204423559480974217317377224914891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-582675446315230439790541080747006000000000000)
      constant := (8221239694594603433422273007887585482703059235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183606658830723583667/50000000000000000000)
  centralHi := (73442663532289433467/20000000000000000000)
  directionLo := (370597843748998402079/100000000000000000000)
  directionHi := (2316236523431240013/625000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree056.table
  base := (-870810430043569382688355663984545334641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-232843788514030244947389219755701622000000000000)
      constant := (3344170089680259530638299710048284222350979153995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree056.table
  base := (-2177058901420352122749466382866531430091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-296630964175079587448772765091233000000000000)
      constant := (4265204258005579088102543063367525331584010247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370597843748998402079/100000000000000000000)
  centralHi := (2316236523431240013/625000000000000000)
  directionLo := (186975869375493987763/50000000000000000000)
  directionHi := (373951738750987975527/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree057.table
  base := (-198083266289247831542002870930971851879/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-118499386920669646008450965642104346000000000000)
      constant := (1733833619223274386106272860198637244057868994810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree057.table
  base := (-1980860833072640444214942224628839197939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-33547133910282661666919443312107000000000000)
      constant := (491411732930454254697042807823148032192870807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186975869375493987763/50000000000000000000)
  centralHi := (373951738750987975527/100000000000000000000)
  directionLo := (188637909789076655911/50000000000000000000)
  directionHi := (377275819578153311823/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree058.table
  base := (-3543984691027473821319441043846598539759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-723461277505945017259243928438147286000000000000)
      constant := (10780354950652279976331049084003309357077522772403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree058.table
  base := (-1772016515789283809790349197107130367487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-307217446210008322555777214526693000000000000)
      constant := (4583123680869134141021788606687852856961183179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188637909789076655911/50000000000000000000)
  centralHi := (377275819578153311823/100000000000000000000)
  directionLo := (1902854337317017401/500000000000000000)
  directionHi := (380570867463403480201/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree059.table
  base := (-775257955787522176071519342705917212997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-122654372247978693077963677170611416000000000000)
      constant := (1860761601949073269432639502455291154145979086966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree059.table
  base := (-620214658538871043362052514340107400357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-625021374454945380218558878488846000000000000)
      constant := (9492916717417304475015347647520985230003504845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1902854337317017401/500000000000000000)
  centralHi := (380570867463403480201/100000000000000000000)
  directionLo := (191918815052959011311/50000000000000000000)
  directionHi := (383837630105918022623/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree060.table
  base := (-329103111194174107205767484783011010763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-124731864911633216612720032934864951000000000000)
      constant := (1925940898765165670523440081334621078571301244628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree060.table
  base := (-2632860458730140067325011411898564155533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-23541031721847189456502345478678000000000000)
      constant := (363904407502198000094948605195785659561723043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191918815052959011311/50000000000000000000)
  centralHi := (383837630105918022623/100000000000000000000)
  directionLo := (19353841182618482561/5000000000000000000)
  directionHi := (387076823652369651221/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree061.table
  base := (-1069689594960421743899348783999831564403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-380428072725863220442429166097355458000000000000)
      constant := (5976791017874541381664347043683039905613065485351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree061.table
  base := (-1069704846595457485501910294620623232571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-323097169262401425216283888679883000000000000)
      constant := (5081877000292025526263850655206731638369188407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19353841182618482561/5000000000000000000)
  centralHi := (387076823652369651221/100000000000000000000)
  directionLo := (390289134530142667343/100000000000000000000)
  directionHi := (24393070908133916709/6250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree062.table
  base := (-324141522293041397365629707353284961359/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-257773700477884527364465488926744042000000000000)
      constant := (4119459774731122392805565836561959468589872566005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree062.table
  base := (-162073376606818985948432156317461243249/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-328390410279865792769786113397613000000000000)
      constant := (5253960764548815444277017133883734505313372665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390289134530142667343/100000000000000000000)
  centralHi := (24393070908133916709/6250000000000000000)
  directionLo := (393475221145840299583/100000000000000000000)
  directionHi := (6148050330403754681/1562500000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree063.table
  base := (-1076821011379047495505833565475567907387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-261928685805193574433978200455251112000000000000)
      constant := (4256679025042303078174048156340701399837311066693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree063.table
  base := (-1076843433675221260290731888339588661557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-24717307503505937801725062082618000000000000)
      constant := (402145238313617158061480844926492357598036347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393475221145840299583/100000000000000000000)
  centralHi := (6148050330403754681/1562500000000000000)
  directionLo := (396635715460985758579/100000000000000000000)
  directionHi := (19831785773049287929/5000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree064.table
  base := (-126932134558963257124151287121175533597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-399125506698753932255236367975637273000000000000)
      constant := (6594277567259953463217713212827998850377156361298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree064.table
  base := (-5077477577897588225080241851106538117/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-338976892314794527876790562833073000000000000)
      constant := (5606876793632388295803833141110064265803744450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396635715460985758579/100000000000000000000)
  centralHi := (19831785773049287929/5000000000000000000)
  directionLo := (199885612227799042893/50000000000000000000)
  directionHi := (399771224455598085787/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree065.table
  base := (86562097828330521377530309686828452281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-270238656459811668573003623512265252000000000000)
      constant := (4537977790853595263264941948910659283353581789241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree065.table
  base := (17309125222769120935653924073829268449/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-688540266664517790860585575101606000000000000)
      constant := (11575417878431490692935167722880872517206285335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199885612227799042893/50000000000000000000)
  centralHi := (399771224455598085787/100000000000000000000)
  directionLo := (402882331489243038649/100000000000000000000)
  directionHi := (8057646629784860773/2000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree066.table
  base := (176511099480659658701533199637424468921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-137196820893560357821258167520386161000000000000)
      constant := (2341028613305180044210944889548486881489848296562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree066.table
  base := (176507570838683568199270437747349047667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-38840374927747029220421668029837000000000000)
      constant := (663495234225625493356726381885392085877295058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402882331489243038649/100000000000000000000)
  centralHi := (8057646629784860773/2000000000000000000)
  directionLo := (101492399392050671679/25000000000000000000)
  directionHi := (405969597568202686717/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree067.table
  base := (1350712883304406590928882643192467185667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-835645881343289288136087139707838176000000000000)
      constant := (14485269964088032616900492379751616048999540289161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree067.table
  base := (675350395199955705385029941670228724871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-354856615367187630537297236986263000000000000)
      constant := (6158121261344879687733537814576711876877332493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101492399392050671679/25000000000000000000)
  centralHi := (405969597568202686717/100000000000000000000)
  directionLo := (2556459765790994649/625000000000000000)
  directionHi := (409033562526559143841/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree068.table
  base := (2020562934599811532472893881580323045907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-282703612441738809781541758097786462000000000000)
      constant := (4977076049185878001839269534417774783365640475027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree068.table
  base := (505138143834143486045575551861223676329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-360149856384651998090799461703993000000000000)
      constant := (6347701366508180805880650972989031715538014214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2556459765790994649/625000000000000000)
  centralHi := (409033562526559143841/100000000000000000000)
  directionLo := (51509343266029279517/12500000000000000000)
  directionHi := (412074746128234236137/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree069.table
  base := (2715590656497958699308884815579896191857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1570132)
      previous := (785066)
      next := (785066)
      square := (7606121353688131569159569555790000000000000)
      linear := (-542265780281753982705206936911708000000000000)
      constant := (9693790904005386749700007737040461618699410913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree069.table
  base := (1357790891822692069709947890742475438353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (358474943618066338446581655000000000000)
      linear := (-25585878134993794416040165681000000000000)
      constant := (457900818875130080811263260724742475438353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51509343266029279517/12500000000000000000)
  centralHi := (412074746128234236137/100000000000000000000)
  directionLo := (207546824548178057927/50000000000000000000)
  directionHi := (83018729819271223171/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree070.table
  base := (3435792763855157627195747249876465413863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-873040749289070711761701543464401806000000000000)
      constant := (15843723960074511018610345880009703782040592363829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree070.table
  base := (858946291308736886696800770721400847593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-370736338419580733197803911139453000000000000)
      constant := (6735609326590258409310902959036637536612341638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207546824548178057927/50000000000000000000)
  centralHi := (83018729819271223171/20000000000000000000)
  directionLo := (418090754075725707583/100000000000000000000)
  directionHi := (6532668032433214181/1562500000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree071.table
  base := (4181166485799781806722569930665174116109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-295168568423665950990079892683307672000000000000)
      constant := (5436753829053262570373021086631201258732636401549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree071.table
  base := (2090579989674122312507069075648119570133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-376029579437045100751306135857183000000000000)
      constant := (6933937138725390946077560072418610091820209639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418090754075725707583/100000000000000000000)
  centralHi := (6532668032433214181/1562500000000000000)
  directionLo := (84213305306724324121/20000000000000000000)
  directionHi := (210533263266810810303/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree072.table
  base := (61896368562193680752648919820363353871/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-149661776875487499029796302105907371000000000000)
      constant := (2797276451093253103366737238757169300816961009240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree072.table
  base := (2475851957248204168506146646291084789213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-14123067424241091418696605947219000000000000)
      constant := (264265956144125289280810282575175983853493677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84213305306724324121/20000000000000000000)
  centralHi := (210533263266810810303/50000000000000000000)
  directionLo := (424021415603704158179/100000000000000000000)
  directionHi := (21201070780185207909/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree073.table
  base := (5747419789519247634058554982320148237383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-910435617234852135387315947220965436000000000000)
      constant := (17263915585074465060655367268293624071856178843989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree073.table
  base := (718426877628935397819777637088616265191/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-386616061471973835858310585292643000000000000)
      constant := (7339340344164823128619009880691300824462892212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424021415603704158179/100000000000000000000)
  centralHi := (21201070780185207909/5000000000000000000)
  directionLo := (42695585487735068187/10000000000000000000)
  directionHi := (426955854877350681871/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree074.table
  base := (6568295735754892167341052107003120440931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-307633524405593092198618027268828882000000000000)
      constant := (5917010698231390609876858881448562847416895761891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree074.table
  base := (1642072913588041753861063408743995155743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-391909302489438203411812810010373000000000000)
      constant := (7546415711800791700911814765390442965618954538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42695585487735068187/10000000000000000000)
  centralHi := (426955854877350681871/100000000000000000000)
  directionLo := (429870263146370086211/100000000000000000000)
  directionHi := (107467565786592521553/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree075.table
  base := (7414335919905616239022297051109830329697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-311788509732902139268130738797335952000000000000)
      constant := (6081669403927991499702320417009145308992942645217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree075.table
  base := (1482866485411425668152144591468223733139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (234876)
      previous := (117438)
      next := (117438)
      square := (1137799471043742558229450172970000000000000)
      linear := (-88267231890422793547847785495134000000000000)
      constant := (1723645979753591537464309975547100355322457965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429870263146370086211/100000000000000000000)
  centralHi := (107467565786592521553/25000000000000000000)
  directionLo := (2704781531879365517/625000000000000000)
  directionHi := (432765045100698482721/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree076.table
  base := (8285539157398888456029856956388024139157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-947830485180633559012930350977529066000000000000)
      constant := (18745843916399837782018090754752260745822506464831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree076.table
  base := (8285536168629400903217976939285406644417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-804991569048733877037634518891666000000000000)
      constant := (15938627854153373734279198407517149463102208011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2704781531879365517/625000000000000000)
  centralHi := (432765045100698482721/100000000000000000000)
  directionLo := (108910147996091748411/25000000000000000000)
  directionHi := (87128118396873398729/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree077.table
  base := (4590952224282285275313088557850195520037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-160049240193760116703578080927175046000000000000)
      constant := (3208923198618472064968592061205312614389926369957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree077.table
  base := (1147737736432625687841352594708183645531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-407789025541831306072319484163563000000000000)
      constant := (8185136759304364163105019287950833948036477092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108910147996091748411/25000000000000000000)
  centralHi := (87128118396873398729/20000000000000000000)
  directionLo := (438497282212751972723/100000000000000000000)
  directionHi := (109624320553187993181/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree078.table
  base := (2020686189943488683928096265556957364177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-324253465714829280476668873382857162000000000000)
      constant := (6589364674504088824568512022952308692989484782485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree078.table
  base := (10103428762216367349758548706032093248877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-30598686411799679527838645102318000000000000)
      constant := (622509288860957614750085199461934977328655933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438497282212751972723/100000000000000000000)
  centralHi := (109624320553187993181/25000000000000000000)
  directionLo := (88267096390772926681/20000000000000000000)
  directionHi := (220667740976932316703/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree079.table
  base := (11050117948775456581063427562868402161837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-985225353126414982638544754734092696000000000000)
      constant := (20289508399815182696154549766701956525734931899271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree079.table
  base := (11050116077692160078386497598214278549587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-836751015153520082358647867198046000000000000)
      constant := (17251059686020902439921624701940798540523751121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88267096390772926681/20000000000000000000)
  centralHi := (220667740976932316703/50000000000000000000)
  directionLo := (444155545676208013939/100000000000000000000)
  directionHi := (22207777283810400697/5000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree080.table
  base := (751372802793718520574859675307158194219/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-166281718184723687307847148219935651000000000000)
      constant := (3469630385083366039486259087087317049907410378072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree080.table
  base := (12021963244464825107186374792337602957739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-847337497188448817465652316633506000000000000)
      constant := (17700200170458000163999471221503437983045386137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444155545676208013939/100000000000000000000)
  centralHi := (22207777283810400697/5000000000000000000)
  directionLo := (446957816665521838457/100000000000000000000)
  directionHi := (223478908332760919229/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree081.table
  base := (13018971130153496976127331699487386060921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-336718421696756421685207007968378372000000000000)
      constant := (7117638582341850683584355695116012762543044460281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree081.table
  base := (3254742440432323569835827549363407231463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-15887481096729213936530680853129000000000000)
      constant := (336206893433410184851889873234280484850887854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446957816665521838457/100000000000000000000)
  centralHi := (223478908332760919229/50000000000000000000)
  directionLo := (44974262751254784651/10000000000000000000)
  directionHi := (449742627512547846511/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree082.table
  base := (70205681884393725384054065557656595009/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-511310110536098203132079579245328163000000000000)
      constant := (10947454351090439794570888706755433684170691334700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree082.table
  base := (14041135206826821362317447641459420916087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-868510461258306287679661215504426000000000000)
      constant := (18615975904822517021490003735677776908944470621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44974262751254784651/10000000000000000000)
  centralHi := (449742627512547846511/100000000000000000000)
  directionLo := (181004120229511013/40000000000000000)
  directionHi := (452510300573777532501/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree083.table
  base := (15088460223356139522685634573082419645447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-345028392351374515824232431025392512000000000000)
      constant := (7481253723293156217364696911970370373819811480967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree083.table
  base := (3017691844607836285018360089807822344589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-879096943293235022786665664939886000000000000)
      constant := (19082611143618094875773607343899793632738823435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181004120229511013/40000000000000000)
  centralHi := (452510300573777532501/100000000000000000000)
  directionLo := (455261148406989167/100000000000000000)
  directionHi := (455261148406989167001/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree084.table
  base := (16160942364397392968531935104719287951289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-349183377678683562893745142553899582000000000000)
      constant := (7666491048327673942641032577302125931787994025529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree084.table
  base := (323218830185864731301953492183455707549/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-49426856962675764327426117465297000000000000)
      constant := (1086393219860591995343915295708766605197006575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455261148406989167/100000000000000000)
  centralHi := (455261148406989167001/100000000000000000000)
  directionLo := (228997737091619937497/50000000000000000000)
  directionHi := (91599094836647974999/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree085.table
  base := (17258582542362722389917643175092952376319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-1060015089017977829889773562247219956000000000000)
      constant := (23562044623153791289614259244504326463603704446077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree085.table
  base := (17258581811476011774761355465601961196013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-900269907363092493000674563810806000000000000)
      constant := (20033376342810704520707432305816452811762653679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228997737091619937497/50000000000000000000)
  centralHi := (91599094836647974999/20000000000000000000)
  directionLo := (460713572076850011623/100000000000000000000)
  directionHi := (57589196509606251453/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree086.table
  base := (18381380539750181037483589398863311107551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-357493348333301657032770565610913722000000000000)
      constant := (8043825200243269736085028119151519350928664527711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree086.table
  base := (18381379915107669360551780279750046620847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-910856389398021228107679013246266000000000000)
      constant := (20517506296514825167547774123980665915885557701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460713572076850011623/100000000000000000000)
  centralHi := (57589196509606251453/12500000000000000000)
  directionLo := (463415727634799851343/100000000000000000000)
  directionHi := (28963482977174990709/6250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree087.table
  base := (2441167021617732348401999077201302329931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-180824166830305352051141638569710396000000000000)
      constant := (4117961012436599293591181192086269140590991563564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree087.table
  base := (19529335639159534632823644200099224810483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-34127513756775924563506794914138000000000000)
      constant := (778054363556199455411825810668748489924745507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463415727634799851343/100000000000000000000)
  centralHi := (28963482977174990709/6250000000000000000)
  directionLo := (466102218126851576683/100000000000000000000)
  directionHi := (116525554531712894171/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree088.table
  base := (10351224643462960708473274529784252971477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-548704978481879626757693983001891793000000000000)
      constant := (12645458021106648418904956380050663292821971995391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree088.table
  base := (10351224415418900696526110983551695030141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-466014676733939349160843956058593000000000000)
      constant := (10751630449568015486244235973580492860115503903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466102218126851576683/100000000000000000000)
  centralHi := (116525554531712894171/25000000000000000000)
  directionLo := (29298332054850732791/6250000000000000000)
  directionHi := (468773312877611724657/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree089.table
  base := (21900719750841877903659309560009337034753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-369958304315228798241308700196434932000000000000)
      constant := (8626975167102560668187633514454960711442296431233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree089.table
  base := (21900719361181733477707512797062025189743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-942615835502807433428692361552646000000000000)
      constant := (22004885544028816002031600300101400905785099269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29298332054850732791/6250000000000000000)
  centralHi := (468773312877611724657/100000000000000000000)
  directionLo := (235714636790829868003/50000000000000000000)
  directionHi := (471429273581659736007/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree090.table
  base := (23124147454220403529513567954573747185691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-374113289642537845310821411724942002000000000000)
      constant := (8825931483347612118057548552088017735579394788251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree090.table
  base := (11562073560674459169381292419117522727873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-17651894769217336454364755759039000000000000)
      constant := (416895217576687855672689134800723169523044817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235714636790829868003/50000000000000000000)
  centralHi := (471429273581659736007/100000000000000000000)
  directionLo := (47407035460278626263/10000000000000000000)
  directionHi := (474070354602786262631/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree091.table
  base := (24372732303809215412967223150107075873047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-1134804824909540677141002369760347216000000000000)
      constant := (27081522886848719411192873499959659944616265973701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree091.table
  base := (609318300487003150049876600327393052591/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-481894399786332451821350630211783000000000000)
      constant := (11512814756580495101823746357812311099403145060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47407035460278626263/10000000000000000000)
  centralHi := (474070354602786262631/100000000000000000000)
  directionLo := (238348401629154856641/50000000000000000000)
  directionHi := (476696803258309713283/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree092.table
  base := (6411618555223373187799769636019090496983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (785066)
      previous := (392533)
      next := (392533)
      square := (3803060676844065784579784777895000000000000)
      linear := (-361458658125856275472445023423399000000000000)
      constant := (8724672593068698939297050613047731062164985294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree092.table
  base := (12823236989026587343156935188569001328079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (1998)
      previous := (999)
      next := (999)
      square := (9678823477687791138057704685000000000000)
      linear := (-920959623447631038515789895897000000000000)
      constant := (22254015912080439198127707669575363035858133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238348401629154856641/50000000000000000000)
  centralHi := (476696803258309713283/100000000000000000000)
  directionLo := (239654430044685260961/50000000000000000000)
  directionHi := (479308860089370521923/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree093.table
  base := (26945373139033658213322530137759660183939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-386578245624464986519359546310463212000000000000)
      constant := (9436519406526073535440627803557784830757555282179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree093.table
  base := (3368171616456175159571845567636560325371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-54720097980140131880928342183027000000000000)
      constant := (1337205539648172935831470783577802884945455108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239654430044685260961/50000000000000000000)
  centralHi := (479308860089370521923/100000000000000000000)
  directionLo := (60238344889754904699/12500000000000000000)
  directionHi := (481906759118039237593/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree094.table
  base := (3533678625269426426034088799773799366743/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-586099846427661050383308386758455423000000000000)
      constant := (14466932556719567962450475400211592279534317139476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree094.table
  base := (1766839301566768734511419660490041235433/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-497774122838725554481857304364973000000000000)
      constant := (12300241074215292948098706022217956071725516312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60238344889754904699/12500000000000000000)
  centralHi := (481906759118039237593/100000000000000000000)
  directionLo := (121122682023004061943/25000000000000000000)
  directionHi := (484490728092016247773/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree095.table
  base := (14809320881468542505858970993403946754341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-197444108139541540329192484683738676000000000000)
      constant := (4927505248531010990271379173865137763470789140901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree095.table
  base := (2961864161173597599759637657156423163877/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-503067363856189922035359529082703000000000000)
      constant := (12568548069303154447829825759897985960248275955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121122682023004061943/25000000000000000000)
  centralHi := (484490728092016247773/100000000000000000000)
  directionLo := (487060988717647299157/100000000000000000000)
  directionHi := (243530494358823649579/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree096.table
  base := (15496505690723988768251358525762311482227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-199521600803196063863948840447992211000000000000)
      constant := (5033842892024453013289547952111373715770406562547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree096.table
  base := (15496505626180784810929924834616155152027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-18828170550876084799587472362979000000000000)
      constant := (475547068215427601562762396262375946075422283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487060988717647299157/100000000000000000000)
  centralHi := (243530494358823649579/50000000000000000000)
  directionLo := (244808878440964778223/50000000000000000000)
  directionHi := (489617756881929556447/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree097.table
  base := (32392537823998555142987804830814249713837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-1209594560801103524392231177273474476000000000000)
      constant := (30847942695753879075458978174005916530964771515271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree097.table
  base := (32392537713802961950736840425326341080417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1027307691782237314284727957036326000000000000)
      constant := (26227818783037561781361848700413388129651596011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244808878440964778223/50000000000000000000)
  centralHi := (489617756881929556447/100000000000000000000)
  directionLo := (492161242864137368091/100000000000000000000)
  directionHi := (123040310716034342023/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree098.table
  base := (8454305265542379957689474033677374723109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-203676586130505110933461551976499281000000000000)
      constant := (5249947920254844650189570013514536916006836257098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree098.table
  base := (3381722096810913418265884254356861422701/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-518947086908583024695866203235893000000000000)
      constant := (13390963718210249192517443225550749258502191915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492161242864137368091/100000000000000000000)
  centralHi := (123040310716034342023/25000000000000000000)
  directionLo := (494691651537654851209/100000000000000000000)
  directionHi := (49469165153765485121/10000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree099.table
  base := (3526706107199189093105293509978893978469/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-205754078794159634468217907740752816000000000000)
      constant := (5359715304844788536869284353714768658295492807545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree099.table
  base := (35267060991711637566706630096538209854591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-38832616883410917944397661329898000000000000)
      constant := (1012661764572047116366626049863380713013078639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494691651537654851209/100000000000000000000)
  centralHi := (49469165153765485121/10000000000000000000)
  directionLo := (248604591281281780959/50000000000000000000)
  directionHi := (497209182562563561919/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree100.table
  base := (36742057833254591020308301663966142068383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-1246989428746884948017845581030038106000000000000)
      constant := (32823755618032585574240306772533310763509915216989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree100.table
  base := (7348411552948387438326794417162579664857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1059067137887023519605741305342706000000000000)
      constant := (27907639403828100767816569468692265626765762655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248604591281281780959/50000000000000000000)
  centralHi := (497209182562563561919/100000000000000000000)
  directionLo := (499714030569497607233/100000000000000000000)
  directionHi := (249857015284748803617/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree101.table
  base := (38242211328919692542387515075273492053929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-419818128242937363075461238538519772000000000000)
      constant := (11165359629377924060852366209320329330938870230569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree101.table
  base := (19121105635227508953410624529703446041659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-534826809960976127356372877389083000000000000)
      constant := (14239621358664907605695792396805872319813015497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499714030569497607233/100000000000000000000)
  centralHi := (249857015284748803617/50000000000000000000)
  directionLo := (251103192667622665667/50000000000000000000)
  directionHi := (100441277067049066267/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree102.table
  base := (39767521544628574004595758327467774379987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-423973113570246410144973950067026842000000000000)
      constant := (11391753879710180786500296925952639616132162221907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree102.table
  base := (39767521494742700605872904059767748317979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (234876)
      previous := (117438)
      next := (117438)
      square := (1137799471043742558229450172970000000000000)
      linear := (-120026677995208998868861133801514000000000000)
      constant := (3228519731527656483383033509004999416580632673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251103192667622665667/50000000000000000000)
  centralHi := (100441277067049066267/20000000000000000000)
  directionLo := (504686431950545946989/100000000000000000000)
  directionHi := (50468643195054594699/10000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree103.table
  base := (20658994234142422147888736549605112823541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-60532769190907077558839663718852000000000000)
      constant := (1643006120785146357892702495720208064050959567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree103.table
  base := (41317988425722698539049094857559950576447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1090826583991809724926754653649086000000000000)
      constant := (29639944002915665483337185664430416774083392501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504686431950545946989/100000000000000000000)
  centralHi := (50468643195054594699/10000000000000000000)
  directionLo := (507154350980500977471/100000000000000000000)
  directionHi := (7924286734070327773/1562500000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree104.table
  base := (670212688901595250915435816039992487363/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-216141542112432252141999686562020491000000000000)
      constant := (5925700930504724682508916809911116532891891886176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree104.table
  base := (857872241067832428645235823691771390683/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-550706533013369230016879551542273000000000000)
      constant := (15114520987343604093388218853723691269328132225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507154350980500977471/100000000000000000000)
  centralHi := (7924286734070327773/1562500000000000000)
  directionLo := (509610318617993939713/100000000000000000000)
  directionHi := (254805159308996969857/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree105.table
  base := (22247196200153203926787595969434920926671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-218219034776086775676756042326274026000000000000)
      constant := (6042327795935587616133440422241736366512746846031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree105.table
  base := (44494392369331973143842368564504607005767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-41185168446728414634843094537778000000000000)
      constant := (1141628574034937383828652027655562937106050743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509610318617993939713/100000000000000000000)
  centralHi := (254805159308996969857/50000000000000000000)
  directionLo := (512054506830487166791/100000000000000000000)
  directionHi := (64006813353810895849/12500000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree106.table
  base := (46120329392885083800641659166182567592139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-1321779164638447795269074388543165366000000000000)
      constant := (36960587448453331795439351391701295490161399207137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree106.table
  base := (46120329366464739627933543076343051032479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1122586030096595930247768001955466000000000000)
      constant := (31424732575582859455511707195945723797896897557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512054506830487166791/100000000000000000000)
  centralHi := (64006813353810895849/12500000000000000000)
  directionLo := (514487083500541883567/100000000000000000000)
  directionHi := (32155442718783867723/6250000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree107.table
  base := (23885711530687221884898308247027239519117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-222374020103395822746268753854781096000000000000)
      constant := (6279011266907612557257266933962095647816847181837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree107.table
  base := (4777142303884047297917485651029856409643/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-566586256065762332677386225695463000000000000)
      constant := (16015662602260441249379240815286653195494654845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514487083500541883567/100000000000000000000)
  centralHi := (32155442718783867723/6250000000000000000)
  directionLo := (516908212560386473429/100000000000000000000)
  directionHi := (51690821256038647343/10000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree108.table
  base := (4944767340068059521559926167697485602329/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-224451512767050346281025109619034631000000000000)
      constant := (6399067872417465517644708729191891720477261614845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree108.table
  base := (49447673381462882150284050067612496145699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-42361444228387162980065811141718000000000000)
      constant := (1209027755025408017336503538820751010461074771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516908212560386473429/100000000000000000000)
  centralHi := (51690821256038647343/10000000000000000000)
  directionLo := (103863610824167635853/20000000000000000000)
  directionHi := (259659027060419089633/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree109.table
  base := (25574540203264030812096988081480394313889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-679587016292114609447344396149864498000000000000)
      constant := (19560803173779350547385437159816339959449088812387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree109.table
  base := (51149080390139873472644593043045676033523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1154345476201382135568781350261846000000000000)
      constant := (33262005119018385689624199040643705390786809009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103863610824167635853/20000000000000000000)
  centralHi := (259659027060419089633/50000000000000000000)
  directionLo := (104343352918973030309/20000000000000000000)
  directionHi := (260858382297432575773/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree110.table
  base := (52875644075331939442407225416834268604663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-457212996188718786701075642295083402000000000000)
      constant := (13285221646849014047507273875655041745726614106743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree110.table
  base := (10575128812271554256254137062663376050251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1164931958236310870675785799697306000000000000)
      constant := (33886092404467804333851299924862765000628675165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104343352918973030309/20000000000000000000)
  centralHi := (260858382297432575773/50000000000000000000)
  directionLo := (8189132762750916949/1562500000000000000)
  directionHi := (524104496816058684737/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree111.table
  base := (54627364404089928208846068575994808564713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-461367981516027833770588353823590472000000000000)
      constant := (13532194337806422689480653297331835945329348274793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree111.table
  base := (5462736439217511344718966961754789800909/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-65306580015068866987932791618487000000000000)
      constant := (1917556180110681083176598985397796257070212915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8189132762750916949/1562500000000000000)
  centralHi := (524104496816058684737/100000000000000000000)
  directionLo := (65810175019033696617/12500000000000000000)
  directionHi := (526481400152269572937/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree112.table
  base := (28202120695145573373882115499134974091263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-698284450265005321260151598028146313000000000000)
      constant := (20672180283066552232150408474698780001992989948029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree112.table
  base := (56404241380132977598224238519726617890411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1186104922306168340889794698568226000000000000)
      constant := (35151761631556630391364835995427847283328740313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65810175019033696617/12500000000000000000)
  centralHi := (526481400152269572937/100000000000000000000)
  directionLo := (264423810307323839053/50000000000000000000)
  directionHi := (528847620614647678107/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree113.table
  base := (58206275031839128036476335472907819417561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-469677952170645927909613776880604612000000000000)
      constant := (14032999199551084732903629943804623499230278559321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree113.table
  base := (14551568755794816853711731675738395524179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-598345702170548537998399574001843000000000000)
      constant := (17896671786565803462338825956272017006543697314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264423810307323839053/50000000000000000000)
  centralHi := (528847620614647678107/100000000000000000000)
  directionLo := (13280082524057748953/2500000000000000000)
  directionHi := (531203300962309958121/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree114.table
  base := (15008366331746697621722889589190063791397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-236916468748977487489563244204555841000000000000)
      constant := (7143415685158383760369112397220096189195180757834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree114.table
  base := (60033465319604788247891558782759915115391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-44713995791704659670511244349598000000000000)
      constant := (1349657669136769506294192185388611995096041839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13280082524057748953/2500000000000000000)
  centralHi := (531203300962309958121/100000000000000000000)
  directionLo := (533548580802849272811/100000000000000000000)
  directionHi := (133387145200712318203/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree115.table
  base := (6188581227428152551259162225502235589747/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159135000000000000000000000000000000000000000
      center := (2355198)
      previous := (1177599)
      next := (1177599)
      square := (11409182030532197353739354333685000000000000)
      linear := (-1355353278332506678776859735172832000000000000)
      constant := (41237098396030049844084390592505447010574388845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree115.table
  base := (61885812267989278917003244531852378609197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3996)
      previous := (1998)
      next := (1998)
      square := (19357646955375582276115409370000000000000)
      linear := (-2302201074500859255596990636814000000000000)
      constant := (70120986979621652243331641544720014222448319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533548580802849272811/100000000000000000000)
  centralHi := (133387145200712318203/25000000000000000000)
  directionLo := (267941798344442102957/50000000000000000000)
  directionHi := (107176719337776841183/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree116.table
  base := (31881657936259415096529392758692272282743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-241071454076286534559075955733062911000000000000)
      constant := (7400677595796907520707662518928433127506591237623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree116.table
  base := (12752663173431170322941809072319319671593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1228450850445883281317812496310066000000000000)
      constant := (37753078709696029536461264045675660214346814095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267941798344442102957/50000000000000000000)
  centralHi := (107176719337776841183/20000000000000000000)
  directionLo := (269104241105419423373/50000000000000000000)
  directionHi := (538208482210838846747/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree117.table
  base := (65665976120703157874904478281061656117123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-486297893479882116187664622994632892000000000000)
      constant := (15062046842092832741841086811510329951555929132803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree117.table
  base := (13133195223226506509648879652182821704879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-45890271573363408015733960953538000000000000)
      constant := (1422888402189163721017689250280059563409404955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269104241105419423373/50000000000000000000)
  centralHi := (538208482210838846747/100000000000000000000)
  directionLo := (540523368086130910103/100000000000000000000)
  directionHi := (67565421010766363763/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree118.table
  base := (67593793018014865654502154037314422211907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-1471358636421573489771532003569419886000000000000)
      constant := (45975074957477152135060162221108838163225594603081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree118.table
  base := (67593793014119799209500628264637540326493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1249623814515740751531821395180986000000000000)
      constant := (39088726560442607249788159308287245988483299519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540523368086130910103/100000000000000000000)
  centralHi := (67565421010766363763/12500000000000000000)
  directionLo := (542828382244936683389/100000000000000000000)
  directionHi := (54282838224493668339/10000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree119.table
  base := (69546766563782311766610470089575201110939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-494607864134500210326690046051647032000000000000)
      constant := (15590289622788699589231368205365402810741968529179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree119.table
  base := (69546766560463181804540121101536759568321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1260210296550669486638825844616446000000000000)
      constant := (39765297813692242091326101753216593536914328843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542828382244936683389/100000000000000000000)
  centralHi := (54282838224493668339/10000000000000000000)
  directionLo := (272561824956346013889/50000000000000000000)
  directionHi := (545123649912692027779/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree120.table
  base := (35762448378729151469893622371436950208963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-249381424730904628698101378790077051000000000000)
      constant := (7928920376489354218868789490317137585921683999043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree120.table
  base := (71524896754630141320533630124792686628353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (234876)
      previous := (117438)
      next := (117438)
      square := (1137799471043742558229450172970000000000000)
      linear := (-141199642065066469082870032672434000000000000)
      constant := (4494188957649857637485688551388125993679196211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272561824956346013889/50000000000000000000)
  centralHi := (545123649912692027779/100000000000000000000)
  directionLo := (136852323422369995151/25000000000000000000)
  directionHi := (109481858737895996121/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree121.table
  base := (36764091799300107988259081958246128104921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-754376752183677456698573203662991758000000000000)
      constant := (24191517564589889776837851903626007867404324632843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree121.table
  base := (36764091798095279557423403970250579481493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-640691630310263478426417371743683000000000000)
      constant := (20567967487952946901675349276144867026734164519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136852323422369995151/25000000000000000000)
  centralHi := (109481858737895996121/20000000000000000000)
  directionLo := (549685433626447367957/100000000000000000000)
  directionHi := (274842716813223683979/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree122.table
  base := (2361144596464163210135466689513088600111/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-253536410058213675767614090318584121000000000000)
      constant := (8199901246515181238487675229969557979297400797936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree122.table
  base := (37778313542400138142978665495180496017721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-645984871327727845979919596461413000000000000)
      constant := (20915000442429425833837081587611589024621109043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549685433626447367957/100000000000000000000)
  centralHi := (274842716813223683979/50000000000000000000)
  directionLo := (275976093649692600823/50000000000000000000)
  directionHi := (551952187299385201647/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree123.table
  base := (77610227221936136221589195567502118328701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-511227805443736398604740892165675312000000000000)
      constant := (16674213102888438248488055133631030304401720932861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree123.table
  base := (77610227220187208390081905149967261576781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-48242823136680904706179394161418000000000000)
      constant := (1575181420211248375860408668196836681374117149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275976093649692600823/50000000000000000000)
  centralHi := (551952187299385201647/100000000000000000000)
  directionLo := (554209669879600468333/100000000000000000000)
  directionHi := (277104834939800234167/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree124.table
  base := (79688984003629470659400206336866113436439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-1546148372313136337022760811082547146000000000000)
      constant := (50852730617898766128200084007272499716148676804037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree124.table
  base := (39844492001069817400399872400333289161543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-656571353362656581086924045896873000000000000)
      constant := (21617813679218716619657071534786372369094318669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554209669879600468333/100000000000000000000)
  centralHi := (277104834939800234167/50000000000000000000)
  directionLo := (69557249275275023549/12500000000000000000)
  directionHi := (556457994202200188393/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree125.table
  base := (16358579486353074207458687682578129190589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-519537776098354492743766315222689452000000000000)
      constant := (17229893802262871830423950939010134842981925764145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree125.table
  base := (81792897430496324282275729252026293108421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1323729188760241897280852541229206000000000000)
      constant := (43947187923057730075182057231176191544467577143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69557249275275023549/12500000000000000000)
  centralHi := (556457994202200188393/100000000000000000000)
  directionLo := (558697270831902298071/100000000000000000000)
  directionHi := (69837158853987787259/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree126.table
  base := (41960983753109560904735121471056293230191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-261846380712831769906639513375598261000000000000)
      constant := (8755581945888793843918799526220417313671041952751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree126.table
  base := (83921967505138210942037474387294773313643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-49419098918339653051402110765358000000000000)
      constant := (1654243705168996149544170128288346935082917147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558697270831902298071/100000000000000000000)
  centralHi := (69837158853987787259/12500000000000000000)
  directionLo := (560927608126481963289/100000000000000000000)
  directionHi := (56092760812648196329/10000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree127.table
  base := (430380971134509944730575393721551444599/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-791771620129458880324187607419555388000000000000)
      constant := (26692080711764857437969203087966098047811650531700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree127.table
  base := (86076194225981379151408529479960718528339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1344902152830099367494861440100126000000000000)
      constant := (45387803707951732559921366021673510942740265937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560927608126481963289/100000000000000000000)
  centralHi := (56092760812648196329/10000000000000000000)
  directionLo := (22525964491918253653/4000000000000000000)
  directionHi := (281574556148978170663/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree128.table
  base := (8825557759375518795730180856864232711373/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-266001366040140816976152224904105331000000000000)
      constant := (9040281775229746867413895798630003793588459035265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree128.table
  base := (44127788796485576770630922924014125466789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-677744317432514051300932944767793000000000000)
      constant := (23058429464111729356785566634257837754042147287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22525964491918253653/4000000000000000000)
  centralHi := (281574556148978170663/50000000000000000000)
  directionLo := (282680943735802772119/50000000000000000000)
  directionHi := (565361887471605544239/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree129.table
  base := (90460117606744802633448769543906345100319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-536157717407590681021817161336717732000000000000)
      constant := (18368693119626163673153885633607751408124551379359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree129.table
  base := (11307514700759640233834749323186045979797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-75893062049997602094937241053947000000000000)
      constant := (2602874761132091117811380166735963019879751356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282680943735802772119/50000000000000000000)
  centralHi := (565361887471605544239/100000000000000000000)
  directionLo := (283783017871461301583/50000000000000000000)
  directionHi := (567566035742922603167/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree130.table
  base := (46344907132928753232232452995985629066589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-810469054102349592136994809297837203000000000000)
      constant := (27988663773014759974656327557842491502023931566487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree130.table
  base := (46344907132644472666213262855460881183273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-688330799467442786407937394203253000000000000)
      constant := (23796232012207064555919411351391937765940688259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283783017871461301583/50000000000000000000)
  centralHi := (567566035742922603167/100000000000000000000)
  directionLo := (1139523314465161131/200000000000000000)
  directionHi := (569761657232580565501/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree131.table
  base := (47472333785548480842801323475566602836963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-272233844031104387580421292196865936000000000000)
      constant := (9475905868805271608866323159762864733594093107043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree131.table
  base := (94944667570612833467085208971581061623971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1387248080969814307922879237841966000000000000)
      constant := (48339013900333014378141144658425308303175177793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1139523314465161131/200000000000000000)
  centralHi := (569761657232580565501/100000000000000000000)
  directionLo := (571948850139500458561/100000000000000000000)
  directionHi := (285974425069750229281/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree132.table
  base := (19444935504496158063391140541964878628943/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-548622673389517822230355295922238942000000000000)
      constant := (19246800786428372274653080613725994780055436879115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree132.table
  base := (3038271172564643123538930137183668018953/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-25885825240828574870923771986619000000000000)
      constant := (909099913483973678381909896393550566112418192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571948850139500458561/100000000000000000000)
  centralHi := (285974425069750229281/50000000000000000000)
  directionLo := (114825542158419941267/20000000000000000000)
  directionHi := (17941490962253115823/3125000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree133.table
  base := (99529844120038027969104395437612314976721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-1658332976150480607899604022352238036000000000000)
      constant := (58632228985390470319160493977829817057196208512243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree133.table
  base := (99529844119687071670341935288335175922297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1408421045039671778136888136712886000000000000)
      constant := (49849608307819263032583744099138759317698168051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114825542158419941267/20000000000000000000)
  centralHi := (17941490962253115823/3125000000000000000)
  directionLo := (576298333697796674011/100000000000000000000)
  directionHi := (144074583424449168503/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree134.table
  base := (101860167363806985047252414578933946835447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-556932644044135916369380718979253082000000000000)
      constant := (19843638363716111717095876799133743046005969070967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree134.table
  base := (25465041840877049263515778012195713648533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-709503763537300256621946293074173000000000000)
      constant := (25306826419693818652274962651455024756083993678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576298333697796674011/100000000000000000000)
  centralHi := (144074583424449168503/25000000000000000000)
  directionLo := (289230405795421661693/50000000000000000000)
  directionHi := (578460811590843323387/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree135.table
  base := (3256738976682295365479704865361293796019/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-280543814685722481719446715253880076000000000000)
      constant := (10072743446093247044220141037022854379474956592944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree135.table
  base := (52107823626789545635668783589839332876097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-26473963131657949043535130288589000000000000)
      constant := (951546831904451382965016935792665007091455313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289230405795421661693/50000000000000000000)
  centralHi := (578460811590843323387/100000000000000000000)
  directionLo := (580615235478554476831/100000000000000000000)
  directionHi := (18144226108704827401/3125000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree136.table
  base := (106596283790169192713876295624866398497057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-1695727844096262031525218426108801666000000000000)
      constant := (61348865741624783198443378882894848991566925730531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree136.table
  base := (106596283789952665461244669986262055847919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1440180491144457983457901485019266000000000000)
      constant := (52159236558178230889066182420607076943675827077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580615235478554476831/100000000000000000000)
  centralHi := (18144226108704827401/3125000000000000000)
  directionLo := (291380847342999447687/50000000000000000000)
  directionHi := (4662093557487991163/800000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree137.table
  base := (54501038486435343521023580104228706675297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-284698800013031528788959426782387146000000000000)
      constant := (10378021714390864809559203714434443545933541486817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree137.table
  base := (54501038486343187748810254401070986275109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-725383486589693359282452967227363000000000000)
      constant := (26470387872701013286830864907994242896967381847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291380847342999447687/50000000000000000000)
  centralHi := (4662093557487991163/800000000000000000)
  directionLo := (58490027689921426559/10000000000000000000)
  directionHi := (584900276899214265591/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree138.table
  base := (111433026801998073455452124351093689952663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1570132)
      previous := (785066)
      next := (785066)
      square := (7606121353688131569159569555790000000000000)
      linear := (-1084220388191629687424256266716978000000000000)
      constant := (39819946005495722600837568383308956956707801767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree138.table
  base := (111433026801841192663088346425275748526877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (444)
      previous := (222)
      next := (222)
      square := (2150849661708398030679489930000000000000)
      linear := (-306942544678495159351377942426000000000000)
      constant := (11285054922182867588054455950743827245580631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58490027689921426559/10000000000000000000)
  centralHi := (584900276899214265591/100000000000000000000)
  directionLo := (58703106820700524909/10000000000000000000)
  directionHi := (587031068207005249091/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree139.table
  base := (14236141659701783761823922927531412912301/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-866561356021021727575416414932682648000000000000)
      constant := (32063618907377705624584149123404999462605745109532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree139.table
  base := (5694456663874037224043509084937444638121/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-735969968624622094389457416662823000000000000)
      constant := (27260674387755478860088483563295747217662822430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58703106820700524909/10000000000000000000)
  centralHi := (587031068207005249091/100000000000000000000)
  directionLo := (589154153141380967083/100000000000000000000)
  directionHi := (147288538285345241771/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree140.table
  base := (116370396399784240478602771681663921275003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-581862556007990198786456988150295502000000000000)
      constant := (21689026932815793686486012758458185454086642111483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree140.table
  base := (116370396399670598897341319412617943901837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1482526419284172923885919282761106000000000000)
      constant := (55320382618397938480988915329605262092749937871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589154153141380967083/100000000000000000000)
  centralHi := (147288538285345241771/25000000000000000000)
  directionLo := (73908701839585707619/12500000000000000000)
  directionHi := (591269614716685660953/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree141.table
  base := (59438408084287191457565501308766487415829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-293008770667649622927984849839401286000000000000)
      constant := (11002297210299789852062721683097990366032106296469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree141.table
  base := (59438408084238834593104377577471564779587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-27650238913316697388757846892529000000000000)
      constant := (1039356444688417233175027155713276457768401523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73908701839585707619/12500000000000000000)
  centralHi := (591269614716685660953/100000000000000000000)
  directionLo := (296688767233736889509/50000000000000000000)
  directionHi := (593377534467473779019/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree142.table
  base := (30352098146013005953297925910566546391511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-885258789993912439388223616810964463000000000000)
      constant := (33483672602405309473932008187073582993378772591626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree142.table
  base := (24281678516793944094761420275296281886149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1503699383354030394099928181632026000000000000)
      constant := (56935944959841701940864057632960655970899330835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296688767233736889509/50000000000000000000)
  centralHi := (593377534467473779019/100000000000000000000)
  directionLo := (297738996242589190551/50000000000000000000)
  directionHi := (595477992485178381103/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree143.table
  base := (30991281411571249610875409756551859694363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-297163755994958669997497561367908356000000000000)
      constant := (11321294437914027112217220050250813327158351896886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree143.table
  base := (30991281411553740441288126432163682912869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-757142932694479564603466315533743000000000000)
      constant := (28876236729200213379222667319920851766089015854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297738996242589190551/50000000000000000000)
  centralHi := (595477992485178381103/100000000000000000000)
  directionLo := (149392766863404879591/25000000000000000000)
  directionHi := (119514213490723903673/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree144.table
  base := (31636753838835326314173491654245170981567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-299241248658613193532253917132161891000000000000)
      constant := (11482507921636752523908725563666486890042164072574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree144.table
  base := (12654701535528170986725484221219380651637/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-28238376804146071561369205194499000000000000)
      constant := (1084719139052808903947218878879861261823579865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149392766863404879591/25000000000000000000)
  centralHi := (119514213490723903673/20000000000000000000)
  directionLo := (14991420917084928217/2500000000000000000)
  directionHi := (599656836683397128681/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree145.table
  base := (8072128856955551377330214103349454826097/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-903956223966803151201030818689246278000000000000)
      constant := (34934593955910409590738087843038118367660800774808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree145.table
  base := (16144257713904764216464128424088877509863/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-767729414729408299710470764969203000000000000)
      constant := (29701512555598218738226599708639855749893492916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14991420917084928217/2500000000000000000)
  centralHi := (599656836683397128681/100000000000000000000)
  directionLo := (300867688072605490361/50000000000000000000)
  directionHi := (601735376145210980723/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree146.table
  base := (131786264714195074002011997904228269199103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-606792467971844481203533257321337922000000000000)
      constant := (23616729257828737224846178301721083679496707091583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree146.table
  base := (131786264714151929533586172778580786623351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1546045311493745334527945979373866000000000000)
      constant := (60237048265435664509803843802817425375341322333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300867688072605490361/50000000000000000000)
  centralHi := (601735376145210980723/100000000000000000000)
  directionLo := (301903380251074148221/50000000000000000000)
  directionHi := (603806760502148296443/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree147.table
  base := (26888724872825409099504627309451578132713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-610947453299153528273045968849844992000000000000)
      constant := (23946015704939273467817653215252941087424323613965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree147.table
  base := (67221812182045169159642670829222902388267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-86479544084926337201941690489407000000000000)
      constant := (3393161276198351192227091212948740746090179729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301903380251074148221/50000000000000000000)
  centralHi := (603806760502148296443/100000000000000000000)
  directionLo := (605871063140977875809/100000000000000000000)
  directionHi := (60587106314097787581/10000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree148.table
  base := (137126140661151028258313192072919905657617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-1845307315879387726027676041135056186000000000000)
      constant := (72832765935816761487880338226453916859966072441011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree148.table
  base := (17140767582639974917016982863507733662589/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-783609137781801402370977439122393000000000000)
      constant := (30961294614800678782367070590195927839611034748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605871063140977875809/100000000000000000000)
  centralHi := (60587106314097787581/10000000000000000000)
  directionLo := (303964178101243916899/50000000000000000000)
  directionHi := (607928356202487833799/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree149.table
  base := (139833813605332500288878718474560069241333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-619257423953771622412071391906859132000000000000)
      constant := (24611448078828045782376750267372026583253508650613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree149.table
  base := (34958453401326483309238362369908252697613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-788902378799265769924479663840123000000000000)
      constant := (31387053519764855041763754336428661146560012958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303964178101243916899/50000000000000000000)
  centralHi := (607928356202487833799/100000000000000000000)
  directionLo := (38123669413181402029/6250000000000000000)
  directionHi := (121995742122180486493/20000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree150.table
  base := (142566643196736030365421568564742028553431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-623412409281080669481584103435366202000000000000)
      constant := (24947594005607011697435183557397513987708451874391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree150.table
  base := (142566643196713430265405489369057712787251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-58829305171609639813183843596878000000000000)
      constant := (2356720607457640851378446133822931530064455779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38123669413181402029/6250000000000000000)
  centralHi := (121995742122180486493/20000000000000000000)
  directionLo := (306011098051205972779/50000000000000000000)
  directionHi := (612022196102411945559/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree151.table
  base := (2270697334928518811546996428026906679707/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-941351091912584574826645222445809908000000000000)
      constant := (37929039638414262639386079183332724448125147215392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree151.table
  base := (145324629435405979298233502017558346579009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1598977721668389010062968226551166000000000000)
      constant := (64494637315082045944032251123656321864187985547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306011098051205972779/50000000000000000000)
  centralHi := (612022196102411945559/100000000000000000000)
  directionLo := (76757360156606003113/12500000000000000000)
  directionHi := (122811776250569604981/20000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree152.table
  base := (37026943080365641721547663781207091246487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-315861189967849381810304763246190171000000000000)
      constant := (12813372669417943493186230682291683112833951456814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree152.table
  base := (5924310892857848570827064928121531932177/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1609564203703317745169972675986626000000000000)
      constant := (65363649780707833554467145780484628014682102275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76757360156606003113/12500000000000000000)
  centralHi := (122811776250569604981/20000000000000000000)
  directionLo := (616088833504535642323/100000000000000000000)
  directionHi := (154022208376133910581/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree153.table
  base := (37729017963727396028451274784324690428859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-317938682631503905345061119010443706000000000000)
      constant := (12984875372643246164366708313987012957173831508598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree153.table
  base := (75458035927447837530156533088406218679987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-30002790476634194079203280100409000000000000)
      constant := (1226638774041380459122114429695788889681713123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616088833504535642323/100000000000000000000)
  centralHi := (154022208376133910581/25000000000000000000)
  directionLo := (123622423838470270841/20000000000000000000)
  directionHi := (309056059596175677103/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree154.table
  base := (76874764017913305248986349121962151799013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-960048525885475286639452424324091723000000000000)
      constant := (39472563967442494761933272037089915697407501791279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree154.table
  base := (153749528035814780367784354494247760077031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1630737167773175215383981574857546000000000000)
      constant := (67119169367663042618714614273861544757180233773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123622423838470270841/20000000000000000000)
  centralHi := (309056059596175677103/50000000000000000000)
  directionLo := (310064401784508187037/50000000000000000000)
  directionHi := (24805152142760654963/4000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree155.table
  base := (156608140864272872036891500413058212032177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-644187335917625904829147661077901552000000000000)
      constant := (26662621037861731909876028709925241060796714504497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree155.table
  base := (78304070432131405261898262661797094917513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-820661824904051975245493012146503000000000000)
      constant := (34002838244497086866895962660112787906706838179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310064401784508187037/50000000000000000000)
  centralHi := (24805152142760654963/4000000000000000000)
  directionLo := (622138950829651738097/100000000000000000000)
  directionHi := (311069475414825869049/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree156.table
  base := (79745955170153227717089718122011237562599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-324171160622467475949330186303204311000000000000)
      constant := (13506242961993512263213810896290069595010553166439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree156.table
  base := (9968244396268618655102958930456268905461/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568899735521871279114725086485000000000000)
      linear := (-91772785102390704755443915207137000000000000)
      constant := (3827667509012709358377670239391884790023732856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622138950829651738097/100000000000000000000)
  centralHi := (311069475414825869049/50000000000000000000)
  directionLo := (624142624135621706051/100000000000000000000)
  directionHi := (156035656033905426513/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree157.table
  base := (20300104557998038076760067637839405052129/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-978745959858365998452259626202373538000000000000)
      constant := (41046955955006790904121684903681628749311136089228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree157.table
  base := (40600209115994256883201672016425851946701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-831248306938980710352497461581963000000000000)
      constant := (34898092693683820331042547774480226886709460766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624142624135621706051/100000000000000000000)
  centralHi := (156035656033905426513/25000000000000000000)
  directionLo := (626139885637690452729/100000000000000000000)
  directionHi := (62613988563769045273/10000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree158.table
  base := (165334919235362222909908513800088160499773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-656652291899553046037685795663422762000000000000)
      constant := (27719075175914553316127426280780650226918566539453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree158.table
  base := (5166716226104876078681298709634203989331/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-836541547956445077905999686299693000000000000)
      constant := (35350093582205793942623133075114719369273834768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626139885637690452729/100000000000000000000)
  centralHi := (62613988563769045273/10000000000000000000)
  directionLo := (125626159299703213807/20000000000000000000)
  directionHi := (157032699124629017259/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree159.table
  base := (10518384915905929991850307413783144853157/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-330403638613431046553599253595964916000000000000)
      constant := (14037899770858704740435688052457336844267907538216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree159.table
  base := (84147079327244808751302199271050572138239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189633245173957093038241695495000000000000)
      linear := (-31179066258292942424425996704349000000000000)
      constant := (1326111490617803543939960380122481752661128431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125626159299703213807/20000000000000000000)
  centralHi := (157032699124629017259/25000000000000000000)
  directionLo := (630115416914504905421/100000000000000000000)
  directionHi := (315057708457252452711/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree160.table
  base := (17127855472143582179306893120414989332133/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-997443393831256710265066828080655353000000000000)
      constant := (42652215601120094411153441798474082084178193041195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree160.table
  base := (8563927736071567352880901220993075828313/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-847128029991373813013004135735153000000000000)
      constant := (36262842687108908136538471055610921020557945790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630115416914504905421/100000000000000000000)
  centralHi := (315057708457252452711/50000000000000000000)
  directionLo := (316046903068524175087/50000000000000000000)
  directionHi := (25283752245481934007/4000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree161.table
  base := (174288107436237485259905471178372717563431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1570132)
      previous := (785066)
      next := (785066)
      square := (7606121353688131569159569555790000000000000)
      linear := (-1264871924161588255663939376652068000000000000)
      constant := (54434986300572415838085470110257026660630439479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree161.table
  base := (21786013429529210052128419848207533141543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (1998)
      previous := (999)
      next := (999)
      square := (9678823477687791138057704685000000000000)
      linear := (-1611382364856026806363906163427000000000000)
      constant := (69420776755181107592513586154368413579286644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316046903068524175087/50000000000000000000)
  centralHi := (25283752245481934007/4000000000000000000)
  directionLo := (634066022493163238923/100000000000000000000)
  directionHi := (158516505623290809731/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree162.table
  base := (3546456335979024260552136053560596672667/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-336636116604394617157868320888725521000000000000)
      constant := (14579845799242966368713682057761804176576787584675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree162.table
  base := (177322816798947977914831441847326986499627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-63534408298244633194074710012638000000000000)
      constant := (2754611473764944875252432034748231975858302683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (634066022493163238923/100000000000000000000)
  centralHi := (158516505623290809731/25000000000000000000)
  directionLo := (159008030851389059317/25000000000000000000)
  directionHi := (636032123405556237269/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree163.table
  base := (90191341404813635891225173574429354276743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-1016140827804147422077874029958937168000000000000)
      constant := (44288342905794578984118606790590964850731360814869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree163.table
  base := (90191341404812260596864111174649578327139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-863007753043766915673510809888343000000000000)
      constant := (37653834664117116921294234636890043927246526337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159008030851389059317/25000000000000000000)
  centralHi := (636032123405556237269/100000000000000000000)
  directionLo := (15949804135303293087/2500000000000000000)
  directionHi := (637992165412131723481/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree164.table
  base := (9173385273415743565576856868525940131227/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-340791101931703664227381032417232591000000000000)
      constant := (14946859384567221953775160821081399080928070515470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree164.table
  base := (183467705468312532767112804678975588830487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1736601988122462566454026069212146000000000000)
      constant := (76246660416724481510356609434020472335265845821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15949804135303293087/2500000000000000000)
  centralHi := (637992165412131723481/100000000000000000000)
  directionLo := (159986551046240480177/25000000000000000000)
  directionHi := (639946204184961920709/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree165.table
  base := (186577884775062184736923877011528423780391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-685737189190716375524274776362972252000000000000)
      constant := (30264162094300376847157970332947088512831782934951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree165.table
  base := (186577884775060196585227764535732968746273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (234876)
      previous := (117438)
      next := (117438)
      square := (1137799471043742558229450172970000000000000)
      linear := (-194132052239710144617892279849734000000000000)
      constant := (8576831450791660316275711125293068221400335251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159986551046240480177/25000000000000000000)
  centralHi := (639946204184961920709/100000000000000000000)
  directionLo := (320947147274368643051/50000000000000000000)
  directionHi := (641894294548737286103/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree166.table
  base := (37942644145983273902767923427402781003101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2491799484)
      previous := (1245899742)
      next := (1245899742)
      square := (12070914588303064800256236885038730000000000000)
      linear := (-2069676523554076267781362463674437966000000000000)
      constant := (91910675738083348390399338977604674258557164668915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree166.table
  base := (94856610364957339658024963853921848219513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-878887476096160018334017484041533000000000000)
      constant := (39071068624718145766240777178682703758119304179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320947147274368643051/50000000000000000000)
  centralHi := (641894294548737286103/100000000000000000000)
  directionLo := (643836490498714455941/100000000000000000000)
  directionHi := (321918245249357227971/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree167.table
  base := (192873713332923588946318630173351083616483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (830599828)
      previous := (415299914)
      next := (415299914)
      square := (4023638196101021600085412295012910000000000000)
      linear := (-694047159845334469663300199419986392000000000000)
      constant := (31011908224316920832370281907300888727280164849763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree167.table
  base := (96436856666461076050783308940522772380359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120097619696841512032525778365000000000000)
      linear := (-884180717113624385887519708759263000000000000)
      constant := (39549311496829593515389038533703622757908667597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643836490498714455941/100000000000000000000)
  centralHi := (321918245249357227971/50000000000000000000)
  directionLo := (10090200706534037023/1562500000000000000)
  directionHi := (645772845218178369473/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree168.table
  base := (49014840646032258504184662582924201544477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (415299914)
      previous := (207649957)
      next := (207649957)
      square := (2011819098050510800042706147506455000000000000)
      linear := (-349101072586321758366406455474246731000000000000)
      constant := (15694605514584022286469164542226650327728107169594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree168.table
  base := (196059362584127812592167871325601729273107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379266490347914186076483390990000000000000)
      linear := (-65886959861562129884520143220518000000000000)
      constant := (2965220010733121292570795894289307314785473603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell095.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10090200706534037023/1562500000000000000)
  centralHi := (645772845218178369473/100000000000000000000)
  directionLo := (647703411095434548107/100000000000000000000)
  directionHi := (161925852773858637027/25000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree169.table
  base := (6227192765111779542562731853525526028753/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1245899742)
      previous := (622949871)
      next := (622949871)
      square := (6035457294151532400128118442519365000000000000)
      linear := (-1053535695749928845703488433715500798000000000000)
      constant := (47653200490872103456121484968844857710536518331184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree169.table
  base := (39854033696715181419442194112125320821631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10240195239393683024065051556730000000000000)
      linear := (-1789534398297106241989048316389446000000000000)
      constant := (81029089137842187108418340658798073786476777865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell095.Kernel169
