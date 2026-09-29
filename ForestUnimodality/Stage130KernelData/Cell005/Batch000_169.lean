import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell005.Parameters
import ForestUnimodality.BinomialMassData.Q2_7.Batch000_049
import ForestUnimodality.BinomialMassData.Q2_7.Batch050_099
import ForestUnimodality.BinomialMassData.Q2_7.Batch100_149
import ForestUnimodality.BinomialMassData.Q2_7.Batch150_199
import ForestUnimodality.BinomialMassData.Q37_126.Batch000_049
import ForestUnimodality.BinomialMassData.Q37_126.Batch050_099
import ForestUnimodality.BinomialMassData.Q37_126.Batch100_149
import ForestUnimodality.BinomialMassData.Q37_126.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree000.table
  base := (642134352852829220047681247/100000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (828208516515492650794660880000000000000)
      constant := (224747023498490227016688436450000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree000.table
  base := (642134352852829220047681247/100000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (14907753297278867714303895840000000000000)
      constant := (4045446422972824086300391856100000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree001.table
  base := (5868371523543952248091073966411269526329/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (521791885661151959990844400000000000000)
      constant := (164121545458919713716437856019515546737212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree001.table
  base := (46471745312573382324265939652425076845553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (83151410638262084409899618640000000000000)
      constant := (26317571322222720634715813643225018571428551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (28759549773992591449/100000000000000000000)
  directionHi := (575190995479851829/2000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree002.table
  base := (859444912760650000011291520701451014503/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (215375254806811269187027920000000000000)
      constant := (120024120994684627453014616098203142030420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree002.table
  base := (6738453080428257925567834676215190365961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (32133041601014359391064174720000000000000)
      constant := (19054679527559893804331378197710064687499435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28759549773992591449/100000000000000000000)
  centralHi := (575190995479851829/2000000000000000000)
  directionLo := (40672145338124403341/100000000000000000000)
  directionHi := (20336072669062201671/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree003.table
  base := (100739115059777276541184957090145373477/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-91041376047529421616788560000000000000)
      constant := (87830796902818847018174892173877201792375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree003.table
  base := (24440619921082762196946318242003841516323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-2098369715137040625307918800000000000000)
      constant := (1534116826545603927904131726026242015528349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40672145338124403341/100000000000000000000)
  centralHi := (20336072669062201671/50000000000000000000)
  directionLo := (4981300141136119047/10000000000000000000)
  directionHi := (49813001411361190471/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree004.table
  base := (9210656270976027251883145991442886811279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-397458006901870112420605040000000000000)
      constant := (64228450748481549312682561460100207678953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree004.table
  base := (4425096622529847843748746994027517193171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-69903696473481090646606713120000000000000)
      constant := (9998375567223487566845352643894408994111828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4981300141136119047/10000000000000000000)
  centralHi := (49813001411361190471/100000000000000000000)
  directionLo := (28759549773992591449/50000000000000000000)
  directionHi := (57519099547985182899/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree005.table
  base := (6704382742829957770751348731628313973473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-703874637756210803224421520000000000000)
      constant := (46841869286410217361280698721398197814311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree005.table
  base := (12750872956852314480445874950395579442051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-120922065510728815665442157040000000000000)
      constant := (7220019462088895311023092098774293543642917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28759549773992591449/50000000000000000000)
  centralHi := (57519099547985182899/100000000000000000000)
  directionLo := (2572332331877445913/4000000000000000000)
  directionHi := (32154154148468073913/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree006.table
  base := (4848182165307652619835568421099090338043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-1010291268610551494028238000000000000000)
      constant := (34093346087520761633049187907693632366301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree006.table
  base := (1823353488020721782500349484306685045853/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-19104492727552948964919733440000000000000)
      constant := (578053476319864052113152611156605789443695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2572332331877445913/4000000000000000000)
  centralHi := (32154154148468073913/50000000000000000000)
  directionLo := (14089244435691424127/20000000000000000000)
  directionHi := (17611555544614280159/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree007.table
  base := (863663595963523254240660215359667113571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-1316707899464892184832054480000000000000)
      constant := (24671080069928050652775879630070679179988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree007.table
  base := (801202504665774925018317192972494941783/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-222958803585224265703113044880000000000000)
      constant := (3725509946848939362165086380263237055927688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14089244435691424127/20000000000000000000)
  centralHi := (17611555544614280159/25000000000000000000)
  directionLo := (76090616520168248833/100000000000000000000)
  directionHi := (38045308260084124417/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree008.table
  base := (2395859662495691051852718069629900197561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-1623124530319232875635870960000000000000)
      constant := (17679493081816969048501838007409301382927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree008.table
  base := (2183266309284064410610781265505855140431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-273977172622471990721948488800000000000000)
      constant := (2640042202316624302199257598603639729248754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76090616520168248833/100000000000000000000)
  centralHi := (38045308260084124417/50000000000000000000)
  directionLo := (40672145338124403341/50000000000000000000)
  directionHi := (81344290676248806683/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree009.table
  base := (1581538104401494973189670956614716489557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-1929541161173573566439687440000000000000)
      constant := (12486765845370854561014159416303015426899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree009.table
  base := (1401947239932583750203179741196449292539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-36110615739968857304531548080000000000000)
      constant := (204663420459345895912687187850752610859914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40672145338124403341/50000000000000000000)
  centralHi := (81344290676248806683/100000000000000000000)
  directionLo := (86278649321977774347/100000000000000000000)
  directionHi := (21569662330494443587/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree010.table
  base := (1893182502539682571987045905173241611467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-4471915584055828514487007840000000000000)
      constant := (17274418304956125450906015736212691280269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree010.table
  base := (795326741181848762342301157489267261217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-376013910696967440759619376640000000000000)
      constant := (1256989129571404288529610767392829074220078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86278649321977774347/100000000000000000000)
  centralHi := (21569662330494443587/25000000000000000000)
  directionLo := (22736420441699333681/25000000000000000000)
  directionHi := (3637827270671893389/4000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree011.table
  base := (887970888120281230707700434098977762463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-5084748845764509896094640800000000000000)
      constant := (11603174779708935834890832958692844337241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree011.table
  base := (316541328319336042915737882274283834673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-427032279734215165778454820560000000000000)
      constant := (831954046964496437882065573999037868519182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22736420441699333681/25000000000000000000)
  centralHi := (3637827270671893389/4000000000000000000)
  directionLo := (95384635739883865727/100000000000000000000)
  directionHi := (745192466717842701/781250000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree012.table
  base := (39661295204015777814106009053898356821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-2848791053736595638851136880000000000000)
      constant := (3741484844521429852795558063377288497747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree012.table
  base := (-27204987898889183388790673073588786667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-53116738752384765644143362720000000000000)
      constant := (58751022232750775013676665341819532199895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95384635739883865727/100000000000000000000)
  centralHi := (745192466717842701/781250000000000000)
  directionLo := (4981300141136119047/5000000000000000000)
  directionHi := (99626002822722380941/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree013.table
  base := (-582230198744700366493291636674765800913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-6310415369181872659309906720000000000000)
      constant := (4567528375924459670313759183276639393609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree013.table
  base := (-191253942886375422585495787622668612741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-529069017808710615816125708400000000000000)
      constant := (319992143018103668053615000691787586303412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4981300141136119047/5000000000000000000)
  centralHi := (99626002822722380941/100000000000000000000)
  directionLo := (10369403136938907311/10000000000000000000)
  directionHi := (103694031369389073111/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree014.table
  base := (-283183649887822985711139854547130126337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-3461624315445277020458769840000000000000)
      constant := (1302260499430046939372259956340178231282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree014.table
  base := (-1288805603997926898560136918501145216247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-580087386845958340834961152320000000000000)
      constant := (185855637272430763073644885049850662387951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10369403136938907311/10000000000000000000)
  centralHi := (103694031369389073111/100000000000000000000)
  directionLo := (53804190926076108153/50000000000000000000)
  directionHi := (107608381852152216307/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree015.table
  base := (-1598566584280811454447701979030762427891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-7536081892599235422525172640000000000000)
      constant := (1409315751966284363728623746784663004763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree015.table
  base := (-866364972198804165840314857210527069573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-70122861764800673983755177360000000000000)
      constant := (12442716675468938911840412291473589233802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53804190926076108153/50000000000000000000)
  centralHi := (107608381852152216307/100000000000000000000)
  directionLo := (111385257319096586843/100000000000000000000)
  directionHi := (27846314329774146711/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree016.table
  base := (-1999120275643331692461692808300303865729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-8148915154307916804132805600000000000000)
      constant := (846153776272521587153256261897872939897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree016.table
  base := (-1057638071381026452529288650777414261543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-682124124920453790872632040160000000000000)
      constant := (87896253978546308446020839618412227410238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111385257319096586843/100000000000000000000)
  centralHi := (27846314329774146711/25000000000000000000)
  directionLo := (28759549773992591449/25000000000000000000)
  directionHi := (115038199095970365797/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree017.table
  base := (-2348738123976814122795089237151821455659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-8761748416016598185740438560000000000000)
      constant := (814637919413075287658516139937249810387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree017.table
  base := (-2450023555731706203651838302220570997489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-733142493957701515891467484080000000000000)
      constant := (105891553755275691120910433180936244423737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28759549773992591449/25000000000000000000)
  centralHi := (115038199095970365797/100000000000000000000)
  directionLo := (59289330731689985919/50000000000000000000)
  directionHi := (118578661463379971839/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree018.table
  base := (-2658097488075242973169872843284769582893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-9374581677725279567348071520000000000000)
      constant := (1240026669830055871190532337006612919749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree018.table
  base := (-2747022799558404520133130656930336314393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-87128984777216582323366992000000000000000)
      constant := (17807961110513046698422379893388812193241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59289330731689985919/50000000000000000000)
  centralHi := (118578661463379971839/100000000000000000000)
  directionLo := (15252054501796651253/12500000000000000000)
  directionHi := (4880657440574928401/4000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree019.table
  base := (-91725245209941334127917151419398970773/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-4993707469716980474477852240000000000000)
      constant := (1033126838033466099099084161027315273424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree019.table
  base := (-753444394962034544324997984874468846483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-835179232032196965929138371920000000000000)
      constant := (246781941617974982914489992844704656176556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15252054501796651253/12500000000000000000)
  centralHi := (4880657440574928401/4000000000000000000)
  directionLo := (62679985563280861847/50000000000000000000)
  directionHi := (25071994225312344739/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree020.table
  base := (-3186128998248485106651231728869735448833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-10600248201142642330563337440000000000000)
      constant := (3250900349722481479081422697911851858169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree020.table
  base := (-3255944793084756304541918564977958936673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-886197601069444690947973815840000000000000)
      constant := (362214968319005922643131687257497282906409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62679985563280861847/50000000000000000000)
  centralHi := (25071994225312344739/20000000000000000000)
  directionLo := (2572332331877445913/2000000000000000000)
  directionHi := (128616616593872295651/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree021.table
  base := (-683097843821721324759398191659010659249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-11213081462851323712170970400000000000000)
      constant := (4761568755700768865166009211934626926285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree021.table
  base := (-3477834782574425847557021347300256411923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-104135107789632490662978806640000000000000)
      constant := (56014085049234842362321963420083846048851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2572332331877445913/2000000000000000000)
  centralHi := (128616616593872295651/100000000000000000000)
  directionLo := (32948203448042792789/25000000000000000000)
  directionHi := (131792813792171171157/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree022.table
  base := (-3626859900605860707000901803945530619153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-11825914724560005093778603360000000000000)
      constant := (6573259154850180112160000972381285665929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree022.table
  base := (-3682769712730444821129645831557468073059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-988234339143940140985644703680000000000000)
      constant := (670633665767957984385064019346915602575547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32948203448042792789/25000000000000000000)
  centralHi := (131792813792171171157/100000000000000000000)
  directionLo := (67447122752680601271/50000000000000000000)
  directionHi := (134894245505361202543/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree023.table
  base := (-3823027123879848572839837196041994016789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-12438747986268686475386236320000000000000)
      constant := (8666468979193506704025287467706041882477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree023.table
  base := (-1936670553002694496411086936674112977959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1039252708181187866004480147600000000000000)
      constant := (860266276062928671807760220831555882994494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67447122752680601271/50000000000000000000)
  centralHi := (134894245505361202543/100000000000000000000)
  directionLo := (68962977701197434431/50000000000000000000)
  directionHi := (137925955402394868863/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree024.table
  base := (-160247565839369855143511077092775026991/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-13051581247977367856993869280000000000000)
      constant := (11025810429355015539844010148764370276575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree024.table
  base := (-4051595617620005748103961341641023315023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-121141230802048399002590621280000000000000)
      constant := (119096015868651319551984610836615531153551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68962977701197434431/50000000000000000000)
  centralHi := (137925955402394868863/100000000000000000000)
  directionLo := (140892444356914241271/100000000000000000000)
  directionHi := (17611555544614280159/12500000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree025.table
  base := (-4178100552876770501307055012105961853103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-13664414509686049238601502240000000000000)
      constant := (13639001403630691980179830915258267028279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree025.table
  base := (-26369810344874895621724032856164809393/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1141289446255683316042151035440000000000000)
      constant := (1304499422920332380377393258788728491867040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140892444356914241271/100000000000000000000)
  centralHi := (17611555544614280159/12500000000000000000)
  directionLo := (71898874434981478623/50000000000000000000)
  directionHi := (143797748869962957247/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree026.table
  base := (-1085044489097962095620389511553871009611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-7138623885697365310104567600000000000000)
      constant := (8248062809589771967322771798245805865446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree026.table
  base := (-109434686454845615293742011957615859847/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1192307815292931041060986479360000000000000)
      constant := (1557421272569019003988033799601272298670040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71898874434981478623/50000000000000000000)
  centralHi := (143797748869962957247/100000000000000000000)
  directionLo := (146645505499731188541/100000000000000000000)
  directionHi := (73322752749865594271/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree027.table
  base := (-1123394476438667270504893121610880490883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-7445040516551706000908384080000000000000)
      constant := (9794543615712623991941571497447673127638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree027.table
  base := (-565916626432171713207391453465235896201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-138147353814464307342202435920000000000000)
      constant := (203335008042742020782643919913521108314696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146645505499731188541/100000000000000000000)
  centralHi := (73322752749865594271/50000000000000000000)
  directionLo := (14943900423408357141/10000000000000000000)
  directionHi := (149439004234083571411/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree028.table
  base := (-1159813668375228225690754173522166047843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-7751457147406046691712200560000000000000)
      constant := (11455603166309021003999600290689675330198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree028.table
  base := (-4669903163623876977269904779422912433899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1294344553367426491098657367200000000000000)
      constant := (2121772309180919222975422353587208649979267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14943900423408357141/10000000000000000000)
  centralHi := (149439004234083571411/100000000000000000000)
  directionLo := (76090616520168248833/50000000000000000000)
  directionHi := (152181233040336497667/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree029.table
  base := (-4778003420170640600957387156695898861363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-16115747556520774765032034080000000000000)
      constant := (26456916798977500713275240943128707970459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree029.table
  base := (-4805847195557818282506882180728833500817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1345362922404674216117492811120000000000000)
      constant := (2432268140707579765473506788466751405036761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76090616520168248833/50000000000000000000)
  centralHi := (152181233040336497667/100000000000000000000)
  directionLo := (38718728827984495683/25000000000000000000)
  directionHi := (154874915311937982733/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree030.table
  base := (-2455246349152201453000049059921059058051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-8364290409114728073319833520000000000000)
      constant := (15110769381359884496964682180552586593643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree030.table
  base := (-987159315195510056968853360428388036139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-155153476826880215681814250560000000000000)
      constant := (306793836022372650483130611065057768616215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38718728827984495683/25000000000000000000)
  centralHi := (154874915311937982733/100000000000000000000)
  directionLo := (157522541549083442717/100000000000000000000)
  directionHi := (78761270774541721359/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree031.table
  base := (-1259322287488743911179623425776257687837/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-8670707039969068764123650000000000000000)
      constant := (17100552864737708031085080999132392370282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree031.table
  base := (-2530143786600124178582062060067768751513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1447399660479169666155163698960000000000000)
      constant := (3108097395526403053175297361783150235784258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157522541549083442717/100000000000000000000)
  centralHi := (78761270774541721359/50000000000000000000)
  directionLo := (32025279264534432381/20000000000000000000)
  directionHi := (80063198161336080953/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree032.table
  base := (-5158876458637614331408734395085242984187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-17954247341646818909854932960000000000000)
      constant := (38392231914637653317924510434403299110691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree032.table
  base := (-5179778633365390453265136742484584204181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1498418029516417391173999142880000000000000)
      constant := (3472866815721643362151019336451240756229373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32025279264534432381/20000000000000000000)
  centralHi := (80063198161336080953/50000000000000000000)
  directionLo := (32537716270499522673/20000000000000000000)
  directionHi := (81344290676248806683/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree033.table
  base := (-65945875591926534987390939149080037527/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-9283540301677750145731282960000000000000)
      constant := (21396004678596926965374612558257589492440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree033.table
  base := (-5294663896708608699131047745584346745057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-172159599839296124021426065200000000000000)
      constant := (428358811919274596204728788808186155061409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32537716270499522673/20000000000000000000)
  centralHi := (81344290676248806683/50000000000000000000)
  directionLo := (82605517681464522571/50000000000000000000)
  directionHi := (165211035362929045143/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree034.table
  base := (-5388028605385246779230469315994983325993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-19179913865064181673070198880000000000000)
      constant := (47397927232178797778293832228035116718049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree034.table
  base := (-1351320960049021453216464439427718071819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1600454767590912841211670030720000000000000)
      constant := (4254991819742061463084948294017935413114508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82605517681464522571/50000000000000000000)
  centralHi := (165211035362929045143/100000000000000000000)
  directionLo := (83847775624779917009/50000000000000000000)
  directionHi := (167695551249559834019/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree035.table
  base := (-2748131616214655411613403558149582640287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-9896373563386431527338915920000000000000)
      constant := (26103903920852106501427450292952921517991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree035.table
  base := (-5511933761777792036273637551237147506471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1651473136628160566230505474640000000000000)
      constant := (4671986919189780526775278792748537363830943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83847775624779917009/50000000000000000000)
  centralHi := (167695551249559834019/100000000000000000000)
  directionLo := (85071895494482350999/50000000000000000000)
  directionHi := (170143790988964701999/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree036.table
  base := (-5600644776813633769436536873016784116887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-20405580388481544436285464800000000000000)
      constant := (57219755247478867735238691808882511181791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree036.table
  base := (-2807435313302368680600782922827663101361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-189165722851712032361037879840000000000000)
      constant := (567340989597333987948466695723714449228514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85071895494482350999/50000000000000000000)
  centralHi := (170143790988964701999/100000000000000000000)
  directionLo := (34511459728791109739/20000000000000000000)
  directionHi := (21569662330494443587/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree037.table
  base := (-1425352447907009864838420820710572422343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-10509206825095112908946548880000000000000)
      constant := (31216056788936997542493516510051986087198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree037.table
  base := (-1142863731217370119249634686355559744531/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1753509874702656016268176362480000000000000)
      constant := (5557110647761307922892345741921988124254615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34511459728791109739/20000000000000000000)
  centralHi := (21569662330494443587/12500000000000000000)
  directionLo := (87468755876744383877/50000000000000000000)
  directionHi := (34987502350697753551/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree038.table
  base := (-5798765422061773950571627289589013546159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-21631246911898907199500730720000000000000)
      constant := (67843432816564872648946257612876905176887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree038.table
  base := (-726309242572536589433139464548802886931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1804528243739903741287011806400000000000000)
      constant := (6025000960113743348556426618326630104880984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87468755876744383877/50000000000000000000)
  centralHi := (34987502350697753551/20000000000000000000)
  directionLo := (11080360709117699539/6250000000000000000)
  directionHi := (1418286170767065541/800000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree039.table
  base := (-5892893457039016032192363146040626724401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-22244080173607588581108363680000000000000)
      constant := (73452440441082248903402405817715612929193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree039.table
  base := (-1180701656882203425366771135343739662987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-206171845864127940700649694480000000000000)
      constant := (723293603375610731800328153626722006159095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11080360709117699539/6250000000000000000)
  centralHi := (1418286170767065541/800000000000000000)
  directionLo := (89801665386711419549/50000000000000000000)
  directionHi := (179603330773422839099/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree040.table
  base := (-299197685995213723505462269033530771437/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-11428456717658134981357998320000000000000)
      constant := (39629008844007281243550997967652845999410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree040.table
  base := (-749196554975816489754890230098871376753/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1906564981814399191324682694240000000000000)
      constant := (7010949582048570550114684959471519435048392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89801665386711419549/50000000000000000000)
  centralHi := (179603330773422839099/100000000000000000000)
  directionLo := (181891363533594669449/100000000000000000000)
  directionHi := (3637827270671893389/2000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree041.table
  base := (-3036043465145174580988008651742018677649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-11734873348512475672161814800000000000000)
      constant := (42629589759966107058234412397805869256457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree041.table
  base := (-1520199712101835396400807946683075455693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-1957583350851646916343518138160000000000000)
      constant := (7528847320707799190763467282022784866488276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181891363533594669449/100000000000000000000)
  centralHi := (3637827270671893389/2000000000000000000)
  directionLo := (18415097021550836791/10000000000000000000)
  directionHi := (184150970215508367911/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree042.table
  base := (-3078708569012055252355905746641232794527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-12041289979366816362965631280000000000000)
      constant := (45727528794023555506534482173511370438311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree042.table
  base := (-6165303981310557384022880048389736691667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-223177968876543849040261509120000000000000)
      constant := (895918845249568936316630505511446588424979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18415097021550836791/10000000000000000000)
  centralHi := (184150970215508367911/100000000000000000000)
  directionLo := (11648949043012522873/6250000000000000000)
  directionHi := (186383184688200365969/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree043.table
  base := (-1248010761368952287793279958496938825837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-24695413220442314107538895520000000000000)
      constant := (97844885646184832592354011692607141095705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree043.table
  base := (-1561797587045642433896113378235031228843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2059620088926142366381189026000000000000000)
      constant := (8614158318682690888936925397182949172984076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11648949043012522873/6250000000000000000)
  centralHi := (186383184688200365969/100000000000000000000)
  directionLo := (47147244907389978813/25000000000000000000)
  directionHi := (188588979629559915253/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree044.table
  base := (-632009360856828723194839578497674634709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-12654123241075497744573264240000000000000)
      constant := (52213993495816740991931835872581387785185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree044.table
  base := (-6326548230819166424875009788196497873819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2110638457963390091400024469920000000000000)
      constant := (9181462265239298903164358161132585705544627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47147244907389978813/25000000000000000000)
  centralHi := (188588979629559915253/100000000000000000000)
  directionLo := (95384635739883865727/50000000000000000000)
  directionHi := (38153854295953546291/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree045.table
  base := (-639762197550834227585473419614428833783/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-12960539871929838435377080720000000000000)
      constant := (55601881799098739221109700713494990817595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree045.table
  base := (-6403457185172962459107110783828027524877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-240184091888959757379873323760000000000000)
      constant := (1085015148743423528938050026518834265932749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95384635739883865727/50000000000000000000)
  centralHi := (38153854295953546291/20000000000000000000)
  directionLo := (7716996995632337739/4000000000000000000)
  directionHi := (48231231222702110869/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree046.table
  base := (-6472714449290562118641001927117570257261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-26533913005568358252361794400000000000000)
      constant := (118171686674497373131732092430177008199173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree046.table
  base := (-6477987347270016894083669018298427527049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2212675196037885541437695357760000000000000)
      constant := (10365140771910453976130950231824791592163217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7716996995632337739/4000000000000000000)
  centralHi := (48231231222702110869/25000000000000000000)
  directionLo := (97528378366666740943/50000000000000000000)
  directionHi := (195056756733333481887/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree047.table
  base := (-1309087571366562733691153842078685154469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-27146746267277039633969427360000000000000)
      constant := (125331288432108097695361753127246019593585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree047.table
  base := (-1637550142964205003941185771132717607541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2263693565075133266456530801680000000000000)
      constant := (10981440493256965558090504918410996466097012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97528378366666740943/50000000000000000000)
  centralHi := (195056756733333481887/100000000000000000000)
  directionLo := (197165539713535118407/100000000000000000000)
  directionHi := (24645692464191889801/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree048.table
  base := (-3307925669300239670507821895576399141111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-13879789764492860507788530160000000000000)
      constant := (66341077443885987611546064650965206012223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree048.table
  base := (-1655037856880634798188938865358083732757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-257190214901375665719485138400000000000000)
      constant := (1290444951371143178702426639209762899345236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197165539713535118407/100000000000000000000)
  centralHi := (24645692464191889801/12500000000000000000)
  directionLo := (4981300141136119047/2500000000000000000)
  directionHi := (199252005645444761881/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree049.table
  base := (-1671001812460870495474443936065517219813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-14186206395347201198592346640000000000000)
      constant := (70111959777369772897941585215082758922618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree049.table
  base := (-1671972017011529727663093392999174238569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2365730303149628716494201689520000000000000)
      constant := (12262805675967761603492211306417872826925508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4981300141136119047/2500000000000000000)
  centralHi := (199252005645444761881/100000000000000000000)
  directionLo := (12582303026121758759/6250000000000000000)
  directionHi := (40263369683589628029/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree050.table
  base := (-1687487988015209389648524811761380052549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-14492623026201541889396163120000000000000)
      constant := (73978128951258848820645668635340679264314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree050.table
  base := (-6753452996546575624764331317889577887671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2416748672186876441513037133440000000000000)
      constant := (12927819734870902213441000456756609337690543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12582303026121758759/6250000000000000000)
  centralHi := (40263369683589628029/20000000000000000000)
  directionLo := (203360726690622016707/100000000000000000000)
  directionHi := (50840181672655504177/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree051.table
  base := (-6813726509186167354121264242375640278207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-29598079314111765160399959200000000000000)
      constant := (155878882483571081778200080223370518052551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree051.table
  base := (-6816883736466548731135049893391799127887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-274196337913791574059096953040000000000000)
      constant := (1512113940361970433401287487416316654943119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203360726690622016707/100000000000000000000)
  centralHi := (50840181672655504177/25000000000000000000)
  directionLo := (102692133174041894587/50000000000000000000)
  directionHi := (8215370653923351567/4000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree052.table
  base := (-6875367300773334987319516274409946233633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-30210912575820446542007592160000000000000)
      constant := (163991538641022652874727680479130376364569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree052.table
  base := (-1375642684269410752516798357874998171399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2518785410261371891550708021280000000000000)
      constant := (14306404074410500857895336864064380184083835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102692133174041894587/50000000000000000000)
  centralHi := (8215370653923351567/4000000000000000000)
  directionLo := (10369403136938907311/5000000000000000000)
  directionHi := (207388062738778146221/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree053.table
  base := (-6934906562659782754218797547209985731743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-30823745837529127923615225120000000000000)
      constant := (172294000724010314858664542609530099877799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree053.table
  base := (-1387494262729500660006449578371425131693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2569803779298619616569543465200000000000000)
      constant := (15019938976514716151909990356337009751650345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10369403136938907311/5000000000000000000)
  centralHi := (207388062738778146221/100000000000000000000)
  directionLo := (104686341360449379601/50000000000000000000)
  directionHi := (209372682720898759203/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree054.table
  base := (-1748093216025854165205624172595553703347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-15718289549618904652611429040000000000000)
      constant := (90393034373864362843993473103662248153142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree054.table
  base := (-3497341630724722413393693241054334461173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-291202460926207482398708767680000000000000)
      constant := (1749957279300904706624461849787153857892202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104686341360449379601/50000000000000000000)
  centralHi := (209372682720898759203/100000000000000000000)
  directionLo := (211338666535371361907/100000000000000000000)
  directionHi := (52834666633842840477/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree055.table
  base := (-28191166116631505900038075501195422843/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-16024706180473245343415245520000000000000)
      constant := (94733782721901203493771277536454005012375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree055.table
  base := (-7049872100695328566713938681937452016639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2671840517373115066607214353040000000000000)
      constant := (16495420738011410204094646593241464706565687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211338666535371361907/100000000000000000000)
  centralHi := (52834666633842840477/25000000000000000000)
  directionLo := (213286529523436271989/100000000000000000000)
  directionHi := (21328652952343627199/10000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree056.table
  base := (-7101185009018795780975670904833863394091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-32662245622655172068438124000000000000000)
      constant := (198338333653861923667960721586162956241363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree056.table
  base := (-142061160192196438137558216900931075991/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2722858886410362791626049796960000000000000)
      constant := (17257343208371133276867034589258603995655150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213286529523436271989/100000000000000000000)
  centralHi := (21328652952343627199/10000000000000000000)
  directionLo := (53804190926076108153/25000000000000000000)
  directionHi := (215216763704304432613/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree057.table
  base := (-1788143302800217002146060773630422052073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-16637539442181926725022878480000000000000)
      constant := (103699117012652210860099206769174091270978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree057.table
  base := (-7154258821096274205554083311425523011357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-308208583938623390738320582320000000000000)
      constant := (2003930312614568054643946687040192050284509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53804190926076108153/25000000000000000000)
  centralHi := (215216763704304432613/100000000000000000000)
  directionLo := (27141229903321546719/12500000000000000000)
  directionHi := (217129839226572373753/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree058.table
  base := (-225061680958190554556998100821095867277/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-16943956073036267415826694960000000000000)
      constant := (108323571486711934514167352228037262864976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree058.table
  base := (-3601745149084148998999070779155856923429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2824895624484858241663720684800000000000000)
      constant := (18829500615862629541390129709957258248831514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27141229903321546719/12500000000000000000)
  centralHi := (217129839226572373753/100000000000000000000)
  directionLo := (219026205705527219769/100000000000000000000)
  directionHi := (21902620570552721977/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree059.table
  base := (-226543825229821116047535611964638180203/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-17250372703890608106630511440000000000000)
      constant := (113042475439278865273292466179960523817264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree059.table
  base := (-3625383188422634915719916823410354863663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2875913993522105966682556128720000000000000)
      constant := (19639718713642697923371596018392657584606158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219026205705527219769/100000000000000000000)
  centralHi := (21902620570552721977/10000000000000000000)
  directionLo := (55226573364279696271/25000000000000000000)
  directionHi := (44181258691423757017/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree060.table
  base := (-7294872954129295845432880402467364645303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-35113578669489897594868655840000000000000)
      constant := (235711560490742748738649843582728447482879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree060.table
  base := (-1459219876078880732816160583679412414849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-325214706951039299077932396960000000000000)
      constant := (2274002235508756369271065259340985089322565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55226573364279696271/25000000000000000000)
  centralHi := (44181258691423757017/20000000000000000000)
  directionLo := (111385257319096586843/50000000000000000000)
  directionHi := (222770514638193173687/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree061.table
  base := (-3669198879227533590217783051445511315211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-17863205965599289488238144400000000000000)
      constant := (122763442758851780166197303599881420793523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree061.table
  base := (-366975010416386019128592163801803094203/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-2977950731596601416720227016560000000000000)
      constant := (21308398653647641898863103513987552911737980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111385257319096586843/50000000000000000000)
  centralHi := (222770514638193173687/100000000000000000000)
  directionLo := (112309632150773466497/50000000000000000000)
  directionHi := (44923852860309386599/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree062.table
  base := (-7379987760980972701538261642201226740963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-36339245192907260358083921760000000000000)
      constant := (255530849374894484446755768504591412813259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree062.table
  base := (-7380978503149030387126825080737718785117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3028969100633849141739062460480000000000000)
      constant := (22166848848549541152720880063461713448838661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112309632150773466497/50000000000000000000)
  centralHi := (44923852860309386599/20000000000000000000)
  directionLo := (226452921373452265097/100000000000000000000)
  directionHi := (113226460686726132549/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree063.table
  base := (-11871444277810877125234060277868886393/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-36952078454615941739691554720000000000000)
      constant := (265723384078842020520021082924323622030625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree063.table
  base := (-3710271398742593534800558029772031322973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-342220829963455207417544211600000000000000)
      constant := (2560151762920564356870102609028724053305402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226452921373452265097/100000000000000000000)
  centralHi := (113226460686726132549/50000000000000000000)
  directionLo := (456543699121009493/200000000000000000)
  directionHi := (228271849560504746501/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree064.table
  base := (-7457401119593195163093731284531272552429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-37564911716324623121299187680000000000000)
      constant := (276104429267246608209976940848281092132997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree064.table
  base := (-372910032196004150579977735098281044503/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3131005838708344591776733348320000000000000)
      constant := (23931945424539188982423290343825492955335980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456543699121009493/200000000000000000)
  centralHi := (228271849560504746501/100000000000000000000)
  directionLo := (230076398191940731593/100000000000000000000)
  directionHi := (115038199095970365797/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree065.table
  base := (-3746620378637384661113621676445474453273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-19088872489016652251453410320000000000000)
      constant := (143336965665620503664035893064881678827089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree065.table
  base := (-3746979364786529870020733272704282509041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3182024207745592316795568792240000000000000)
      constant := (24838583731715203818734723071453343634747506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230076398191940731593/100000000000000000000)
  centralHi := (115038199095970365797/50000000000000000000)
  directionLo := (231866903002949572893/100000000000000000000)
  directionHi := (115933451501474786447/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree066.table
  base := (-1505435678018711444884677907638121164153/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-38790578239741985884514453600000000000000)
      constant := (297431842646905962068044659152665759254645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree066.table
  base := (-1881955744305111747886185053840334604981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-359226952975871115757156026240000000000000)
      constant := (2862364158844327195566986534832235679544788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231866903002949572893/100000000000000000000)
  centralHi := (115933451501474786447/50000000000000000000)
  directionLo := (46728737372791053397/20000000000000000000)
  directionHi := (116821843431977633493/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree067.table
  base := (-59056406747707427746236267023889415307/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-19701705750725333633061043280000000000000)
      constant := (154189060447321264628521526773297541942464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree067.table
  base := (-3779899317272734258472508587976481902227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3284060945820087766833239680080000000000000)
      constant := (26700023542754023939803948859774669522874582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46728737372791053397/20000000000000000000)
  centralHi := (116821843431977633493/50000000000000000000)
  directionLo := (29425882557544243811/12500000000000000000)
  directionHi := (235407060460353950489/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree068.table
  base := (-7589371152132307345210945305670746022613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-40016244763159348647729719520000000000000)
      constant := (319512728456320806803172961100304777841709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree068.table
  base := (-3794945176457004086668760462520071029653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3335079314857335491852075124000000000000000)
      constant := (27654819433855985210864941487022239452373498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29425882557544243811/12500000000000000000)
  centralHi := (235407060460353950489/100000000000000000000)
  directionLo := (237157322926759943677/100000000000000000000)
  directionHi := (118578661463379971839/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree069.table
  base := (-3808818217017669357995125535017642881519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-20314539012434015014668676240000000000000)
      constant := (165417815940644606366506558374876499829367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree069.table
  base := (-7618102256908503566959897366388823293687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-376233075988287024096767840880000000000000)
      constant := (3180629196029620716727679051977504132497719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237157322926759943677/100000000000000000000)
  centralHi := (118578661463379971839/50000000000000000000)
  directionLo := (119447381219713493281/50000000000000000000)
  directionHi := (238894762439426986563/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree070.table
  base := (-477751260018759393022685491818369088653/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-20620955643288355705472492720000000000000)
      constant := (171173400706678104537507930858171331035432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree070.table
  base := (-7644438005706742001549654737265726681287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3437116052931830941889746011840000000000000)
      constant := (29612551459232022257637291631570332971710271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119447381219713493281/50000000000000000000)
  centralHi := (238894762439426986563/100000000000000000000)
  directionLo := (60154914192541769977/25000000000000000000)
  directionHi := (240619656770167079909/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree071.table
  base := (-766852611389212836177035378093627240197/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-20927372274142696396276309200000000000000)
      constant := (177023105285882045866546194726723046593105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree071.table
  base := (-3834450423632079917997692698861145673807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3488134421969078666908581455760000000000000)
      constant := (30615483677161560216639650110191460805902862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60154914192541769977/25000000000000000000)
  centralHi := (240619656770167079909/100000000000000000000)
  directionLo := (242332273804781870559/100000000000000000000)
  directionHi := (1514576711279886691/625000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree072.table
  base := (-480697353930492325761294173502953867991/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-21233788904997037087080125680000000000000)
      constant := (182966917889988315387732307083834583392504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree072.table
  base := (-1538298733229057780924275245812263717691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-393239199000702932436379655520000000000000)
      constant := (3514939753611901197499368471329136928927335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242332273804781870559/100000000000000000000)
  centralHi := (1514576711279886691/625000000000000000)
  directionLo := (15252054501796651253/6250000000000000000)
  directionHi := (244032872028746420049/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree073.table
  base := (-1542383561491259113963124012467347774931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-43080411071702755555767884320000000000000)
      constant := (378009656036811535090581383403642827877415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree073.table
  base := (-7712219025750417002496976493386980935641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3590171160043574116946252343600000000000000)
      constant := (32669472321820710760396968995269581809491553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15252054501796651253/6250000000000000000)
  centralHi := (244032872028746420049/100000000000000000000)
  directionLo := (245721700982638658371/100000000000000000000)
  directionHi := (61430425245659664593/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree074.table
  base := (-7730809221482079651512136468173291120971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-43693244333411436937375517280000000000000)
      constant := (390273652625075931160583397362786962153203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree074.table
  base := (-7731079205595728055456142351730255712983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3641189529080821841965087787520000000000000)
      constant := (33720526002616683879399755226808945010738639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245721700982638658371/100000000000000000000)
  centralHi := (61430425245659664593/25000000000000000000)
  directionLo := (247399001689586535657/100000000000000000000)
  directionHi := (123699500844793267829/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree075.table
  base := (-7747834289444071743155642395714815765893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-44306077595120118318983150240000000000000)
      constant := (402725808853417922984272951229996289638749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree075.table
  base := (-7748076234227754591666050930120256307079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-410245322013118840775991470160000000000000)
      constant := (3865290852745460687892431722902423852654023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247399001689586535657/100000000000000000000)
  centralHi := (123699500844793267829/50000000000000000000)
  directionLo := (4981300141136119047/2000000000000000000)
  directionHi := (249065007056805952351/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree076.table
  base := (-3881497569545365517742230175035352117627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-22459455428414399850295391600000000000000)
      constant := (207683054913799148113240893734752535176611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree076.table
  base := (-3881605959142337975853238346020517448553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3743226267155317292002758675360000000000000)
      constant := (35870746313734250009184627712412733213340898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4981300141136119047/2000000000000000000)
  centralHi := (249065007056805952351/100000000000000000000)
  directionLo := (250719942253123447389/100000000000000000000)
  directionHi := (25071994225312344739/10000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree077.table
  base := (-3888146835196462363754061683655721298813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-22765872059268740541099208080000000000000)
      constant := (214097271123910490247071587414409950908309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree077.table
  base := (-7776487868156745751259083465151498752999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3794244636192565017021594119280000000000000)
      constant := (36969911006600721533766478455399100207049567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250719942253123447389/100000000000000000000)
  centralHi := (25071994225312344739/10000000000000000000)
  directionLo := (126182012532108071341/50000000000000000000)
  directionHi := (252364025064216142683/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree078.table
  base := (-3893865790599643506320843763229464296469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-23072288690123081231903024560000000000000)
      constant := (220605547114572768216675860377393749924717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree078.table
  base := (-973488190080622221616699728439682700891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-427251445025534749115603284800000000000000)
      constant := (4231678993182487327781969196146399918750936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126182012532108071341/50000000000000000000)
  centralHi := (252364025064216142683/100000000000000000000)
  directionLo := (31749683278394455209/12500000000000000000)
  directionHi := (253997466227155641673/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree079.table
  base := (-7797310389970747002152795253116403606111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-46757410641954843845413682080000000000000)
      constant := (454415755142345460265233928268185174757223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree079.table
  base := (-7797466158970321518558487325489914567651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3896281374267060467059265007120000000000000)
      constant := (39216345382272964890461619543387218440141883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31749683278394455209/12500000000000000000)
  centralHi := (253997466227155641673/100000000000000000000)
  directionLo := (6390511743642768909/2500000000000000000)
  directionHi := (255620469745710756361/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree080.table
  base := (-1561006291185551303382799115642791937479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-47370243903663525227021315040000000000000)
      constant := (467808515472877589243681954152502282188235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree080.table
  base := (-7805170930444178206615080984631091060577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-3947299743304308192078100451040000000000000)
      constant := (40363613686966893864159255232114171368652841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6390511743642768909/2500000000000000000)
  centralHi := (255620469745710756361/100000000000000000000)
  directionLo := (2572332331877445913/1000000000000000000)
  directionHi := (257233233187744591301/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree081.table
  base := (-390544799845280636718923540465136357161/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-23991538582686103304314474000000000000000)
      constant := (240694683347947421563261761127440454998730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree081.table
  base := (-19527552155186485400803218389475018301/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-444257568037950657455215099440000000000000)
      constant := (4614101696712290067318452853685229538814800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2572332331877445913/1000000000000000000)
  centralHi := (257233233187744591301/100000000000000000000)
  directionLo := (129417973982966661521/50000000000000000000)
  directionHi := (258835947965933323043/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree082.table
  base := (-1562981021035900297782835501845721060641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-48595910427080887990236580960000000000000)
      constant := (495158301165470921073182936635399762877565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree082.table
  base := (-488438554646890482017641935210059403341/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4049336481378803642115771338880000000000000)
      constant := (42706249610687034500994952611214341092890448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129417973982966661521/50000000000000000000)
  centralHi := (258835947965933323043/100000000000000000000)
  directionLo := (130214399801467905921/50000000000000000000)
  directionHi := (260428799602935811843/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree083.table
  base := (-977132470186372879222369649999797046713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-24604371844394784685922106960000000000000)
      constant := (254557656008207450655427653320005682692036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree083.table
  base := (-7817159793415912332589860292603691508233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4100354850416051367134606782800000000000000)
      constant := (43901616239372078992003819265113706914831889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130214399801467905921/50000000000000000000)
  centralHi := (260428799602935811843/100000000000000000000)
  directionLo := (262011967982053936913/100000000000000000000)
  directionHi := (131005983991026968457/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree084.table
  base := (-390868042374057988546741890910853419431/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-24910788475249125376725923440000000000000)
      constant := (261630196538619533512903218356240260639830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree084.table
  base := (-1563490072365597371112937586049002310717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-461263691050366565794826914080000000000000)
      constant := (5012557192826251771092541885354564272124145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262011967982053936913/100000000000000000000)
  centralHi := (131005983991026968457/50000000000000000000)
  directionLo := (263585627584342342313/100000000000000000000)
  directionHi := (131792813792171171157/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree085.table
  base := (-3907904578356156265961433867779134271373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-25217205106103466067529739920000000000000)
      constant := (268796769396503726198624494125546060100389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree085.table
  base := (-7815889248056540278946622452410682981713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4202391588490546817172277670640000000000000)
      constant := (46340444719857066222763620237783142749368729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263585627584342342313/100000000000000000000)
  centralHi := (131792813792171171157/50000000000000000000)
  directionLo := (33143743464131538303/12500000000000000000)
  directionHi := (10605997908522092257/4000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree086.table
  base := (-3906202702219510670778955124170925296033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-25523621736957806758333556400000000000000)
      constant := (276057372078468998625739459090803522927769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree086.table
  base := (-7812477054880776863832694458588839551081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4253409957527794542191113114560000000000000)
      constant := (47583905850858671024754032723980127974537073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33143743464131538303/12500000000000000000)
  centralHi := (10605997908522092257/4000000000000000000)
  directionLo := (266705092706226982799/100000000000000000000)
  directionHi := (666762731765567457/250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree087.table
  base := (-3903575118135695519118456494564143246319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-25830038367812147449137372880000000000000)
      constant := (283412002324879983859858796538050997275767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree087.table
  base := (-7807214326807581272995295186617239754353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-478269814062782474134438728720000000000000)
      constant := (5427044202189519638001352066103113895475761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266705092706226982799/100000000000000000000)
  centralHi := (666762731765567457/250000000000000000)
  directionLo := (268251222138203662383/100000000000000000000)
  directionHi := (16765701383637728899/6250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree088.table
  base := (-3900022117928354886334689427627050692811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-26136454998666488139941189360000000000000)
      constant := (290860658092971173373499246326610645150323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree088.table
  base := (-975012694578447922176315048153190439353/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4355446695602289992228784002400000000000000)
      constant := (50118920346985796237694581561097128167094792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268251222138203662383/100000000000000000000)
  centralHi := (16765701383637728899/6250000000000000000)
  directionLo := (53957698202144481017/20000000000000000000)
  directionHi := (134894245505361202543/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree089.table
  base := (-7791087931691438577070916691980485647471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-52885743259041657661490011680000000000000)
      constant := (596806675066009907107812354996136600467703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree089.table
  base := (-1947784797802437507745431272835175204159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4406465064639537717247619446320000000000000)
      constant := (51410473179324325305638069316549822636967388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53957698202144481017/20000000000000000000)
  centralHi := (134894245505361202543/50000000000000000000)
  directionLo := (33914631241786109021/12500000000000000000)
  directionHi := (271317049934288872169/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree090.table
  base := (-3890140901581324902614981481115564881569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-26749288260375169521548822320000000000000)
      constant := (306040038967126571162820062432191045829017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree090.table
  base := (-7780327636623656471546120326909792931621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-495275937075198382474050543360000000000000)
      constant := (5857561787386646087332103690204683045307877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33914631241786109021/12500000000000000000)
  centralHi := (271317049934288872169/100000000000000000000)
  directionLo := (136418522650196002087/50000000000000000000)
  directionHi := (10913481812015680167/4000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree091.table
  base := (-970953285738339078054723375837366014383/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-27055704891229510212352638800000000000000)
      constant := (313770760870608734114721458436553751597276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree091.table
  base := (-485479203916757979482065441780229071371/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4508501802714033167285290334160000000000000)
      constant := (54041668858776330919277676913269761864522288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136418522650196002087/50000000000000000000)
  centralHi := (10913481812015680167/4000000000000000000)
  directionLo := (34293577430641740521/12500000000000000000)
  directionHi := (274348619445133924169/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree092.table
  base := (-7753121776562997835810227265068473301963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-54724243044167701806312910560000000000000)
      constant := (643191003710427289211409861944520686886259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree092.table
  base := (-7753158406875706352571176767139924404511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4559520171751280892304125778080000000000000)
      constant := (55381311304832921982647023708071662862642263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34293577430641740521/12500000000000000000)
  centralHi := (274348619445133924169/100000000000000000000)
  directionLo := (68962977701197434431/25000000000000000000)
  directionHi := (11034076432191589509/4000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree093.table
  base := (-7736768636991494177902987761948010572267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-55337076305876383187920543520000000000000)
      constant := (659028521308862684101651031906363925994131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree093.table
  base := (-967100172256781891629272382293663116913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-512282060087614290813662358000000000000000)
      constant := (6304109249950614430130324768103993789075848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68962977701197434431/25000000000000000000)
  centralHi := (11034076432191589509/4000000000000000000)
  directionLo := (277347054063778421387/100000000000000000000)
  directionHi := (69336763515944605347/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree094.table
  base := (-7718567198015362927907709983563974231953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-55949909567585064569528176480000000000000)
      constant := (675054072220761523959824936355052180376329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree094.table
  base := (-7718596459419808030310947111397858864497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4661556909825776342341796665920000000000000)
      constant := (58108684532360663297097932100877414023830201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277347054063778421387/100000000000000000000)
  centralHi := (69336763515944605347/25000000000000000000)
  directionLo := (69708545073873111519/25000000000000000000)
  directionHi := (278834180295492446077/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree095.table
  base := (-3849258881371245520680960667444177405211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-28281371414646872975567904720000000000000)
      constant := (345633827162184300048584441727890758163523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree095.table
  base := (-384927195568421941760410509165933868717/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4712575278863024067360632109840000000000000)
      constant := (59496415005603748421034635783158309928749220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69708545073873111519/25000000000000000000)
  centralHi := (278834180295492446077/100000000000000000000)
  directionLo := (280313417096402906379/100000000000000000000)
  directionHi := (14015670854820145319/5000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree096.table
  base := (-7676620609513932522123542053090199914647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-57175576091002427332743442400000000000000)
      constant := (707669265671296534486677431548368600597471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree096.table
  base := (-7676643973929311551698174529779593001467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-529288183100030199153274172640000000000000)
      constant := (6766686059243138805858977001423885640907579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280313417096402906379/100000000000000000000)
  centralHi := (14015670854820145319/5000000000000000000)
  directionLo := (281784888713828482543/100000000000000000000)
  directionHi := (17611555544614280159/6250000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree097.table
  base := (-1913218998630415549231434247100111798589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-28894204676355554357175537680000000000000)
      constant := (362129452234100751670609213340598434819754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree097.table
  base := (-1530579373787226712359610409596412425403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4814612016937519517398302997680000000000000)
      constant := (62319962989334453706582644644134170773982495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281784888713828482543/100000000000000000000)
  centralHi := (17611555544614280159/6250000000000000000)
  directionLo := (283248716167730334581/100000000000000000000)
  directionHi := (141624358083865167291/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree098.table
  base := (-953410519266653124455725620287194286913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-29200621307209895047979354160000000000000)
      constant := (370518284530255346075825388551958559966436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree098.table
  base := (-7627302801949868188473858943963639775969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4865630385974767242417138441600000000000000)
      constant := (63755780257489295578468459488292616247025577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283248716167730334581/100000000000000000000)
  centralHi := (141624358083865167291/50000000000000000000)
  directionLo := (28470501736687082339/10000000000000000000)
  directionHi := (284705017366870823391/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree099.table
  base := (-1519969061391315167330306223421031316659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-59014075876128471477566341280000000000000)
      constant := (758002257917968416489399986820263903916935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree099.table
  base := (-474991372747606980788224457987451093733/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-546294306112446107492885987280000000000000)
      constant := (7245291803262307398718430861208649297517136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28470501736687082339/10000000000000000000)
  centralHi := (284705017366870823391/100000000000000000000)
  directionLo := (286153907219651597181/100000000000000000000)
  directionHi := (143076953609825798591/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree100.table
  base := (-1514111931134921414638648411938936643943/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-59626909137837152859173974240000000000000)
      constant := (775155969621794429881713769582137217461995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree100.table
  base := (-757057453290194027689962857980929446147/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-4967667124049262692454809329440000000000000)
      constant := (66675500804062400129650588323248130040346510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286153907219651597181/100000000000000000000)
  centralHi := (143076953609825798591/50000000000000000000)
  directionLo := (71898874434981478623/25000000000000000000)
  directionHi := (287595497739925914493/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree101.table
  base := (-753942738867549618561358442956658468897/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-30119871199772917120390803600000000000000)
      constant := (396248851426635744983096799456516953588605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree101.table
  base := (-37697203374886161354950310248443630677/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5018685493086510417473644773360000000000000)
      constant := (68159403887355009589109855410126492281228200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71898874434981478623/25000000000000000000)
  centralHi := (287595497739925914493/100000000000000000000)
  directionLo := (289029898148060954383/100000000000000000000)
  directionHi := (18064368634253809649/6250000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree102.table
  base := (-7506448681502026418933306880241080858899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-60852575661254515622389240160000000000000)
      constant := (810027456383600114027694234238312433987707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree102.table
  base := (-7506460545856422468294184912256674251191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-563300429124862015832497801920000000000000)
      constant := (7739926154552707293219941753487829522174967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289029898148060954383/100000000000000000000)
  centralHi := (18064368634253809649/6250000000000000000)
  directionLo := (145228607483754080119/50000000000000000000)
  directionHi := (290457214967508160239/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree103.table
  base := (-7471623698140393448284900603213869608517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-61465408922963197003996873120000000000000)
      constant := (827745229064876932340288237217502912740381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree103.table
  base := (-7471634291722308210787168677985465811553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5120722231161005867511315661200000000000000)
      constant := (71175295232034822186359527190602240884849449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145228607483754080119/50000000000000000000)
  centralHi := (290457214967508160239/100000000000000000000)
  directionLo := (29187755211712325813/10000000000000000000)
  directionHi := (291877552117123258131/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree104.table
  base := (-7434952592166673007993604697984541854339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-62078242184671878385604506080000000000000)
      constant := (845651019822069414763698934154108207019627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree104.table
  base := (-929370256275632971092289236201014841977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5171740600198253592530151105120000000000000)
      constant := (72707283332500070420007316230032196676792328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29187755211712325813/10000000000000000000)
  centralHi := (291877552117123258131/100000000000000000000)
  directionLo := (146645505499731188541/50000000000000000000)
  directionHi := (293291010999462377083/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree105.table
  base := (-739643550776705329222119599382365732777/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-31345537723190279883606069520000000000000)
      constant := (431872413822937121969396943621617199352805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree105.table
  base := (-1479288790242199723972539096867061594249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-580306552137277924172109616560000000000000)
      constant := (8250588846523692540673155045586875597811565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146645505499731188541/50000000000000000000)
  centralHi := (293291010999462377083/100000000000000000000)
  directionLo := (920930283078958061/312500000000000000)
  directionHi := (294697690585266579521/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree106.table
  base := (-7356072580646101312406073922341273983957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-63303908708089241148819772000000000000000)
      constant := (882026651586359450785504300463611082112301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree106.table
  base := (-7356080117658787964075121075961388058461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5273777338272749042567821992960000000000000)
      constant := (75819344020979420686161068814329892970852613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (920930283078958061/312500000000000000)
  centralHi := (294697690585266579521/100000000000000000000)
  directionLo := (29609768749433399737/10000000000000000000)
  directionHi := (296097687494333997371/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree107.table
  base := (-7313863938835707253288313459473346258099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-63916741969797922530427404960000000000000)
      constant := (900496490747301804010649648983686576193307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree107.table
  base := (-457116916633367820164799485039989088371/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5324795707309996767586657436880000000000000)
      constant := (77399416473194681847160235420657218990298288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29609768749433399737/10000000000000000000)
  centralHi := (296097687494333997371/100000000000000000000)
  directionLo := (297491096072966582183/100000000000000000000)
  directionHi := (37186387009120822773/12500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree108.table
  base := (-3634904851707955634045619958182075240351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-32264787615753301956017518960000000000000)
      constant := (459577172140570511270833327812725473317543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree108.table
  base := (-7269815707470573218289589625614265309651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-597312675149693832511721431200000000000000)
      constant := (8777279656946219757606805342866301285491987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297491096072966582183/100000000000000000000)
  centralHi := (37186387009120822773/12500000000000000000)
  directionLo := (14943900423408357141/5000000000000000000)
  directionHi := (298878008468167142821/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree109.table
  base := (-7223909989157541893642550406608998718037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-65142408493215285293642670880000000000000)
      constant := (938000211384481306620761440593737008973741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree109.table
  base := (-7223915347270008171817497296120218593871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5426832445384492217624328324720000000000000)
      constant := (80607645279067453192979588661239836057275143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14943900423408357141/5000000000000000000)
  centralHi := (298878008468167142821/100000000000000000000)
  directionLo := (300258514698751794867/100000000000000000000)
  directionHi := (75064628674687948717/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree110.table
  base := (-7176164905095465569837124677288468850277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-65755241754923966675250303840000000000000)
      constant := (957034091294078591168669845658980718048061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree110.table
  base := (-358808484318081466575828772823699341053/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5477850814421739942643163768640000000000000)
      constant := (82235801515678815860231390738979249472458980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300258514698751794867/100000000000000000000)
  centralHi := (75064628674687948717/25000000000000000000)
  directionLo := (301632702723533120831/100000000000000000000)
  directionHi := (4713010980055205013/1562500000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree111.table
  base := (-1781643638760061495852953230191936290141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-33184037508316324028428968400000000000000)
      constant := (488127991641629465189116959737312891938026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree111.table
  base := (-3563289410607226376429779515283950717727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-614318798162109740851333245840000000000000)
      constant := (9319998396405792635195957068574222209566398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301632702723533120831/100000000000000000000)
  centralHi := (4713010980055205013/1562500000000000000)
  directionLo := (75750164626680045869/25000000000000000000)
  directionHi := (303000658506720183477/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree112.table
  base := (-1768784759508781348193894491038462574459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-33490454139170664719232784880000000000000)
      constant := (497832943329359814220295461125461523957574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree112.table
  base := (-707514284430400183165945277697791067093/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5579887552496235392680834656480000000000000)
      constant := (85540197382553784997150283597693524649582690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75750164626680045869/25000000000000000000)
  centralHi := (303000658506720183477/100000000000000000000)
  directionLo := (304362466080672995333/100000000000000000000)
  directionHi := (152181233040336497667/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree113.table
  base := (-702185844876445468149512436742850841023/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-33796870770025005410036601360000000000000)
      constant := (507631900378835114585386961034000220564195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree113.table
  base := (-109716591319374356386747300522662835143/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5630905921533483117699670100400000000000000)
      constant := (87216436910028679870837632185653611038330816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304362466080672995333/100000000000000000000)
  centralHi := (152181233040336497667/50000000000000000000)
  directionLo := (38214775950767634841/12500000000000000000)
  directionHi := (305718207606141078729/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree114.table
  base := (-348336643895950153850908315753563079697/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-34103287400879346100840417840000000000000)
      constant := (517524862472637673988324459817250584421210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree114.table
  base := (-435420994191189258984851235153948736597/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-631324921174525649190945060480000000000000)
      constant := (9878744900181578545468954210724819673510224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38214775950767634841/12500000000000000000)
  centralHi := (305718207606141078729/100000000000000000000)
  directionLo := (307067963430108309697/100000000000000000000)
  directionHi := (153533981715054154849/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree115.table
  base := (-6909762412522962023203904411002479193163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-68819408063467373583288468640000000000000)
      constant := (1055023658612365644751201510722982645647859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree115.table
  base := (-1727441278621744916290007793490416900337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5732942659607978567737340988240000000000000)
      constant := (90616998910691654619549175871063734470035684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307067963430108309697/100000000000000000000)
  centralHi := (153533981715054154849/50000000000000000000)
  directionLo := (308411812141359286749/100000000000000000000)
  directionHi := (1233647248565437147/400000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree116.table
  base := (-54807577089815292357172857426993696403/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-69432241325176054964896101600000000000000)
      constant := (1075185601173387059322271815671380515647375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree116.table
  base := (-856368693271672199187049998733660532357/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5783961028645226292756176432160000000000000)
      constant := (92341321292153120088778725167344115825228648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308411812141359286749/100000000000000000000)
  centralHi := (1233647248565437147/400000000000000000)
  directionLo := (61949966124775193093/20000000000000000000)
  directionHi := (154874915311937982733/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree117.table
  base := (-1697571782392633389583216272499705509713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-35022537293442368173251867280000000000000)
      constant := (547767776032280909135476850585004122864018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree117.table
  base := (-169757231972552345279722592792520971817/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-648331044186941557530556875120000000000000)
      constant := (10453519022498016439952873460222847151021160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61949966124775193093/20000000000000000000)
  centralHi := (154874915311937982733/50000000000000000000)
  directionLo := (31108209410816721933/10000000000000000000)
  directionHi := (311082094108167219331/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree118.table
  base := (-1345556494043685572413622863985070915751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-70657907848593417728111367520000000000000)
      constant := (1116073510742237723012609114000522517948715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree118.table
  base := (-1681946096745085942087720210121094068859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5885997766719721742793847320000000000000000)
      constant := (95838048599546547071726320864965358651827788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31108209410816721933/10000000000000000000)
  centralHi := (311082094108167219331/100000000000000000000)
  directionLo := (312408676220628295649/100000000000000000000)
  directionHi := (6248173524412565913/2000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree119.table
  base := (-1332686646634401332050816279770492553763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-71270741110302099109719000480000000000000)
      constant := (1136799476681404888116425968448032760618295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree119.table
  base := (-832929367801083195784911587140829566569/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-5937016135756969467812682763920000000000000)
      constant := (97610453442522012321794727267269197086043016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312408676220628295649/100000000000000000000)
  centralHi := (6248173524412565913/2000000000000000000)
  directionLo := (313729649031021804747/100000000000000000000)
  directionHi := (78432412257755451187/25000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree120.table
  base := (-6597239490960106897018880197086923688003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-71883574372010780491326633440000000000000)
      constant := (1157713449374361454973507467420391534183979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree120.table
  base := (-206163781719811940781387928937240190619/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-665337167199357465870168689760000000000000)
      constant := (11044320632422815380607101637662523775712096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313729649031021804747/100000000000000000000)
  centralHi := (78432412257755451187/25000000000000000000)
  directionLo := (157522541549083442717/50000000000000000000)
  directionHi := (63009016619633377087/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree121.table
  base := (-6529201313810661412507839911271162923917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-72496407633719461872934266400000000000000)
      constant := (1178815428329511893702836306541101859532581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree121.table
  base := (-1632300668171909588539593461049803031491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6039052873831464917850353651760000000000000)
      constant := (101203345308936152784952465617039046724578412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157522541549083442717/50000000000000000000)
  centralHi := (63009016619633377087/20000000000000000000)
  directionLo := (316355047513918505941/100000000000000000000)
  directionHi := (158177523756959252971/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree122.table
  base := (-6459318769805505643719572053395637627049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-73109240895428143254541899360000000000000)
      constant := (1200105413070283356245422205226230536610657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree122.table
  base := (-1614829995327521739136777741576279121681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6090071242868712642869189095680000000000000)
      constant := (103023832256526218751789413103944998952027492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316355047513918505941/100000000000000000000)
  centralHi := (158177523756959252971/50000000000000000000)
  directionLo := (79414902486378616399/25000000000000000000)
  directionHi := (317659609945514465597/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree123.table
  base := (-638759192502016237960304045919622748889/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-36861037078568412318074766160000000000000)
      constant := (610791701567073591539311208312813203788885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree123.table
  base := (-199612281408240690684378239983314159333/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-682343290211773374209780504400000000000000)
      constant := (11651149610910607795599793648973638654784672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79414902486378616399/25000000000000000000)
  centralHi := (317659609945514465597/100000000000000000000)
  directionLo := (318958836676363538091/100000000000000000000)
  directionHi := (79739709169090884523/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree124.table
  base := (-6314020843650239517607919163655543130029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-74334907418845506017757165280000000000000)
      constant := (1243249398071734118920289222494411198089797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree124.table
  base := (-1262804361287006182927576431200502284013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6192107980943208092906859983520000000000000)
      constant := (106712887998514034791232214219786576024823145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318958836676363538091/100000000000000000000)
  centralHi := (79739709169090884523/25000000000000000000)
  directionLo := (320252792645344323811/100000000000000000000)
  directionHi := (80063198161336080953/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree125.table
  base := (-311930279406294590697149824257045298157/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-37473870340277093699682399120000000000000)
      constant := (632551698723016540238480552302006829129010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree125.table
  base := (-1559651611581910209102802783607800559507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6243126349980455817925695427440000000000000)
      constant := (108581456722949589904875643634277508331038124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320252792645344323811/100000000000000000000)
  centralHi := (80063198161336080953/25000000000000000000)
  directionLo := (160770770742340369563/50000000000000000000)
  directionHi := (321541541484680739127/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree126.table
  base := (-6161346219215634578563050098107694198061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-75560573942262868780972431200000000000000)
      constant := (1287145400831664460578954619233246140613573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree126.table
  base := (-6161346984146588314955352702758218270393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-699349413224189282549392319040000000000000)
      constant := (12274005848646607610606948608926232248965241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160770770742340369563/50000000000000000000)
  centralHi := (321541541484680739127/100000000000000000000)
  directionLo := (161412572778228324459/50000000000000000000)
  directionHi := (322825145556456648919/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree127.table
  base := (-3041121398060326376107187996799079845943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-38086703601985775081290032080000000000000)
      constant := (654687703907109982320522847222406441078399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree127.table
  base := (-1520560869468854118274368137311903547099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6345163088054951267963366315280000000000000)
      constant := (112366675710247001612349892812716602755179468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161412572778228324459/50000000000000000000)
  centralHi := (322825145556456648919/100000000000000000000)
  directionLo := (324103665987828930287/100000000000000000000)
  directionHi := (20256479124239308143/6250000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree128.table
  base := (-3000647688280310351565712786444658496239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-38393120232840115772093848560000000000000)
      constant := (665896708994830936042796585214887390526327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree128.table
  base := (-1200259196829297101056149826731641229053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6396181457092198992982201759200000000000000)
      constant := (114283325908121641025288427444735797115634745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (324103665987828930287/100000000000000000000)
  centralHi := (20256479124239308143/6250000000000000000)
  directionLo := (325377162704995226731/100000000000000000000)
  directionHi := (81344290676248806683/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree129.table
  base := (-5918504016851934523126890024307873712779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-77399073727388912925795330080000000000000)
      constant := (1354399430963775410269908208869844884010547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree129.table
  base := (-2959252279152673863610601105286785045923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-716355536236605190889004133680000000000000)
      constant := (12912889244451384285696350908393865084213702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (325377162704995226731/100000000000000000000)
  centralHi := (81344290676248806683/25000000000000000000)
  directionLo := (81661423616492450147/25000000000000000000)
  directionHi := (326645694465969800589/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree130.table
  base := (-2916934385989578964279169018696557270989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-39005953494548797153701481520000000000000)
      constant := (688596723175834316589743914469124099103077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree130.table
  base := (-5833869254469798069295631063846831104777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6498218195166694443019872647040000000000000)
      constant := (118164707555384664524762439811198846763591441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81661423616492450147/25000000000000000000)
  centralHi := (326645694465969800589/100000000000000000000)
  directionLo := (327909318892218205479/100000000000000000000)
  directionHi := (8197732972305455137/2500000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree131.table
  base := (-2873694847830196806086042150695368234751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-39312370125403137844505298000000000000000)
      constant := (700087731888657410982553913905132422356743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree131.table
  base := (-5747390125584159104484948216810468958759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6549236564203942168038708090960000000000000)
      constant := (120129438944068827986894094950968464100383647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327909318892218205479/100000000000000000000)
  centralHi := (8197732972305455137/2500000000000000000)
  directionLo := (329168092499198969133/100000000000000000000)
  directionHi := (164584046249599484567/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree132.table
  base := (-2829533420203606372998362363298960307659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-39618786756257478535309114480000000000000)
      constant := (711672741436566489211284017056907277846387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree132.table
  base := (-5659067223469296332497561028892828374217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-733361659249021099228615948320000000000000)
      constant := (13567799704081390913258606291339751812424329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329168092499198969133/100000000000000000000)
  centralHi := (164584046249599484567/50000000000000000000)
  directionLo := (66084414145171618057/20000000000000000000)
  directionHi := (165211035362929045143/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree133.table
  base := (-5568900257579705150789519504369673810149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-79850406774223638452225861920000000000000)
      constant := (1446703503279602473806567626509412283328957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree133.table
  base := (-5568900598868803428076629875050081456229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6651273302278437618076378978800000000000000)
      constant := (124106982704604117608483152891866603814318157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66084414145171618057/20000000000000000000)
  centralHi := (165211035362929045143/50000000000000000000)
  directionLo := (82917826990779975487/25000000000000000000)
  directionHi := (331671307963119901949/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree134.table
  base := (-5476889997437150403207248190199916379861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-80463240035932319833833494880000000000000)
      constant := (1470249524644908351080509148108600585340973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree134.table
  base := (-5476890301491747642932565963913626979353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6702291671315685343095214422720000000000000)
      constant := (126119795019498585022641380605100973502706849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82917826990779975487/25000000000000000000)
  centralHi := (331671307963119901949/100000000000000000000)
  directionLo := (332915857581415728811/100000000000000000000)
  directionHi := (83228964395353932203/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree135.table
  base := (-134575902729618873584246209662905714149/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-40538036648820500607720563920000000000000)
      constant := (746991773312307082581776517847193200019140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree135.table
  base := (-168219886876635055232302533293277179381/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-750367782261437007568227762960000000000000)
      constant := (14238737139310552572184811887580753206367904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (332915857581415728811/100000000000000000000)
  centralHi := (83228964395353932203/25000000000000000000)
  directionLo := (33415577195728976053/10000000000000000000)
  directionHi := (334155771957289760531/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree136.table
  base := (-528733864101685127199110196618615978277/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-40844453279674841298524380400000000000000)
      constant := (758952784440679794275351408078348440760305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree136.table
  base := (-5287338882306710339886236124935663693937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6804328409390180793132885310560000000000000)
      constant := (130193500380415525356329282085161478685537721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33415577195728976053/10000000000000000000)
  centralHi := (334155771957289760531/100000000000000000000)
  directionLo := (335391102499119668037/100000000000000000000)
  directionHi := (167695551249559834019/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree137.table
  base := (-2594898820078455938942154209774857052747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-41150869910529181989328196880000000000000)
      constant := (771007795542290156910132696531576000630771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree137.table
  base := (-5189797855087443545829929524962807736599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6855346778427428518151720754480000000000000)
      constant := (132254393372806197027438296913086088013348367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335391102499119668037/100000000000000000000)
  centralHi := (167695551249559834019/50000000000000000000)
  directionLo := (16831094983599384981/5000000000000000000)
  directionHi := (336621899671987699621/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree138.table
  base := (-5090413152894691984914509907867168755549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-82914573082767045360264026720000000000000)
      constant := (1566313612910248054405185471284929818711157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree138.table
  base := (-5090413344335481954952700007223183868157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-767373905273852915907839577600000000000000)
      constant := (14925701467213162613330810022824939416306109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16831094983599384981/5000000000000000000)
  centralHi := (336621899671987699621/100000000000000000000)
  directionLo := (84462053255434075239/25000000000000000000)
  directionHi := (337848213021736300957/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree139.table
  base := (-1247296306155195248869853832373540524511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-41763703172237863370935829840000000000000)
      constant := (795399817020314342244339544266770432656846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree139.table
  base := (-2494592697565124218904171278044393857821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-6957383516501923968189391642320000000000000)
      constant := (136424259851192292066342260206037657365230986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84462053255434075239/25000000000000000000)
  centralHi := (337848213021736300957/100000000000000000000)
  directionLo := (84767522799560175653/25000000000000000000)
  directionHi := (339070091198240702613/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree140.table
  base := (-305382118741175758868058322397208215923/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-42070119803092204061739646320000000000000)
      constant := (807736827082028385722288442745756339908312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree140.table
  base := (-977222810343559976251015510652755790489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7008401885539171693208227086240000000000000)
      constant := (138533233286540168411684595958499437333963685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84767522799560175653/25000000000000000000)
  centralHi := (339070091198240702613/100000000000000000000)
  directionLo := (340287581977929403997/100000000000000000000)
  directionHi := (170143790988964701999/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree141.table
  base := (-2390599611147776450343188721493258762781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-42376536433946544752543462800000000000000)
      constant := (820167836487362471468537831909547188660533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree141.table
  base := (-4781199357537310321187317453448075825573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-784380028286268824247451392240000000000000)
      constant := (15628692609592453430850240622332771222988901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340287581977929403997/100000000000000000000)
  centralHi := (170143790988964701999/50000000000000000000)
  directionLo := (341500732285582049269/100000000000000000000)
  directionHi := (34150073228558204927/10000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree142.table
  base := (-4674441234809074790658243506277249980297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-85365906129601770886694558560000000000000)
      constant := (1665385690172486698334669956256059250137921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree142.table
  base := (-14607629235143807863340738922889865971/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7110438623613667143245897974080000000000000)
      constant := (142799260426381375088082495762870862718221760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341500732285582049269/100000000000000000000)
  centralHi := (34150073228558204927/10000000000000000000)
  directionLo := (342709588215432833317/100000000000000000000)
  directionHi := (171354794107716416659/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree143.table
  base := (-570729997436897490006836864677165698837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-42989369695655226134151095760000000000000)
      constant := (845311852731335711439804308909039360432564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree143.table
  base := (-142682502710711766155171755632560561543/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7161456992650914868264733418000000000000000)
      constant := (144956314082931401930361783104822821171363808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342709588215432833317/100000000000000000000)
  centralHi := (171354794107716416659/50000000000000000000)
  directionLo := (68782839010321258027/20000000000000000000)
  directionHi := (42989274381450786267/12500000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree144.table
  base := (-4455395497692242768423206422424448582667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-86591572653019133649909824480000000000000)
      constant := (1716049718555910495215059325283028859921331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree144.table
  base := (-891079118638064238573317268669251337167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-801386151298684732587063206880000000000000)
      constant := (16347710492515876622159173350929185828792395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68782839010321258027/20000000000000000000)
  centralHi := (42989274381450786267/12500000000000000000)
  directionLo := (34511459728791109739/10000000000000000000)
  directionHi := (345114597287911097391/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree145.table
  base := (-542888478750576114276008072539166699921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-43602202957363907515758728720000000000000)
      constant := (870831864583986748145956036368903332402212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree145.table
  base := (-1085776978759094437449182803633254529029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7263493730725410318302404305840000000000000)
      constant := (149318501452581977903592378362459778728162228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34511459728791109739/10000000000000000000)
  centralHi := (345114597287911097391/100000000000000000000)
  directionLo := (346310838647016375903/100000000000000000000)
  directionHi := (10822213707719261747/3125000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree146.table
  base := (-4228977016324677512181478881055736135689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-87817239176436496413125090400000000000000)
      constant := (1767465737019613632026761393752609847050177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree146.table
  base := (-528622136504211600450818330917778343211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7314512099762658043321239749760000000000000)
      constant := (151523635120208859511653938528156957435194904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346310838647016375903/100000000000000000000)
  centralHi := (10822213707719261747/3125000000000000000)
  directionLo := (173751481049516933617/50000000000000000000)
  directionHi := (69500592419806773447/20000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree147.table
  base := (-4113003095853781073616624073356575791047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-88430072438145177794732723360000000000000)
      constant := (1793455741836421574840695065086503969462671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree147.table
  base := (-16452012653036337639133397554707226111/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-818392274311100640926675021520000000000000)
      constant := (17082755045929664287350659117773361188751750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173751481049516933617/50000000000000000000)
  centralHi := (69500592419806773447/20000000000000000000)
  directionLo := (34869100987952833329/10000000000000000000)
  directionHi := (348691009879528333291/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree148.table
  base := (-1997593053560982159695230492516904719853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-44521452849926929588170178160000000000000)
      constant := (909816871674343505843787180472381666961029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree148.table
  base := (-249699135445724214163014595994841868133/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7416548837837153493358910637600000000000000)
      constant := (155981982310272742362452978604654794572297424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34869100987952833329/10000000000000000000)
  centralHi := (348691009879528333291/100000000000000000000)
  directionLo := (87468755876744383877/25000000000000000000)
  directionHi := (349875023506977535509/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree149.table
  base := (-968881522001688349008298102105004321993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-44827869480781270278973994640000000000000)
      constant := (922999870645633629770843930890529939492098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree149.table
  base := (-1937763070714882290947687293501880265891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7467567206874401218377746081520000000000000)
      constant := (158235195789505705773874440654908867778479606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87468755876744383877/25000000000000000000)
  centralHi := (349875023506977535509/100000000000000000000)
  directionLo := (351055043799702214687/100000000000000000000)
  directionHi := (10970470118740694209/3125000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree150.table
  base := (-750804615150199484001051903962195568053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-90268572223271221939555622240000000000000)
      constant := (1872553735403462374587812479361323155118145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree150.table
  base := (-750804624661649300425251540326844544533/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-835398397323516549266286836160000000000000)
      constant := (17833826203333243695022812902797043968472105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351055043799702214687/100000000000000000000)
  centralHi := (10970470118740694209/3125000000000000000)
  directionLo := (352231110892285603179/100000000000000000000)
  directionHi := (17611555544614280159/5000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree151.table
  base := (-1815338553489928007877836860727956893781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-45440702742489951660581627600000000000000)
      constant := (949647862714448119727402566934904301743533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree151.table
  base := (-1815338574656778822217569352150431967573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7569603944948896668415416969360000000000000)
      constant := (162789702411031325439250481962961410148772218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352231110892285603179/100000000000000000000)
  centralHi := (17611555544614280159/5000000000000000000)
  directionLo := (353403264251501156113/100000000000000000000)
  directionHi := (176701632125750578057/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree152.table
  base := (-3505488217716999122997160664200880865653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-91494238746688584702770888160000000000000)
      constant := (1926225711115403164564676745750593833940429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree152.table
  base := (-350548825539927945509595605015081296551/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7620622313986144393434252413280000000000000)
      constant := (165090995512216421645972615064204489048555830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353403264251501156113/100000000000000000000)
  centralHi := (176701632125750578057/50000000000000000000)
  directionLo := (354571542691766385249/100000000000000000000)
  directionHi := (1418286170767065541/400000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree153.table
  base := (-3378456443400078765602667855447675274807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-92107072008397266084378521120000000000000)
      constant := (1953343692214919585750316682451866273076351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree153.table
  base := (-3378456476940597082002457884902518382429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-852404520335932457605898650800000000000000)
      constant := (18600923901499639099612884470031141341906973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354571542691766385249/100000000000000000000)
  centralHi := (1418286170767065541/400000000000000000)
  directionLo := (71147196878027983103/20000000000000000000)
  directionHi := (88933996097534978879/25000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree154.table
  base := (-3249581818895526607920641730483642187113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-92719905270105947465986154080000000000000)
      constant := (1980649668483380481361285818926614504690209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree154.table
  base := (-324958184874827152186054361751033905023/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7722659052060639843471923301120000000000000)
      constant := (169741661195134614705748272496311637758519590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71147196878027983103/20000000000000000000)
  centralHi := (88933996097534978879/25000000000000000000)
  directionLo := (356896626900878158127/100000000000000000000)
  directionHi := (22306039181304884883/6250000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree155.table
  base := (-389858047314090736703271426208210420967/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-46666369265907314423796893520000000000000)
      constant := (1004071819840310084345929265666170108212924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree155.table
  base := (-124754576203283004893439286124790527891/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7773677421097887568490758745040000000000000)
      constant := (172091033737704719152543060893081094267145075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356896626900878158127/100000000000000000000)
  centralHi := (22306039181304884883/6250000000000000000)
  directionLo := (358053507169567303311/100000000000000000000)
  directionHi := (22378344198097956457/6250000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree156.table
  base := (-2986304156017601696224901931134583820819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-93945571793523310229201420000000000000000)
      constant := (2035825605570277172227495304402057913254267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree156.table
  base := (-93322005614491400924727061904322872413/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-869410643348348365945510465440000000000000)
      constant := (19384048080231872414269576908800885089215392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358053507169567303311/100000000000000000000)
  centralHi := (22378344198097956457/6250000000000000000)
  directionLo := (89801665386711419549/25000000000000000000)
  directionHi := (359206661546845678197/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree157.table
  base := (-712975296161417311423887117975885972483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-47279202527615995805404526480000000000000)
      constant := (1031847782959851442679172565948337596385238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree157.table
  base := (-2851901205689344423197268237716396447159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7875714159172383018528429632880000000000000)
      constant := (176837858129458810250380981286154803214460847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89801665386711419549/25000000000000000000)
  centralHi := (359206661546845678197/100000000000000000000)
  directionLo := (360356125801730889503/100000000000000000000)
  directionHi := (11261128931304090297/3125000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree158.table
  base := (-33945693713932204707026931016186698017/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-47585619158470336496208342960000000000000)
      constant := (1045876760249936886621369854835467724555240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree158.table
  base := (-2121605871751159507769465690856782603/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-7926732528209630743547265076800000000000000)
      constant := (179235309941289588717136972513723781458046720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360356125801730889503/100000000000000000000)
  centralHi := (11261128931304090297/3125000000000000000)
  directionLo := (22593870945910348413/6250000000000000000)
  directionHi := (361501935134565574609/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree159.table
  base := (-161097945352260801195995291301439474761/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-47892035789324677187012159440000000000000)
      constant := (1059999734542653443884250302407119389413384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree159.table
  base := (-1288783571150361908537907554829359378379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-886416766360764274285122280080000000000000)
      constant := (20183198682148088712445352832551500718324246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22593870945910348413/6250000000000000000)
  centralHi := (361501935134565574609/100000000000000000000)
  directionLo := (181322062094797508363/50000000000000000000)
  directionHi := (362644124189595016727/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree160.table
  base := (-1218818050964068041887271990575473710277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-48198452420179017877815975920000000000000)
      constant := (1074216705726989243181562011265971684028061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree160.table
  base := (-1218818058378441300003628030262912433817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-8028769266284126193584935964640000000000000)
      constant := (184078292705620311828512986370481857300051522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181322062094797508363/50000000000000000000)
  centralHi := (362644124189595016727/100000000000000000000)
  directionLo := (363782727067189338899/100000000000000000000)
  directionHi := (3637827270671893389/1000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree161.table
  base := (-2295862457225181028637227314722017377129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-97009738102066717137239584800000000000000)
      constant := (2177055347387245565019495458716945878360097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree161.table
  base := (-2295862470419857929654083212523682592977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-8079787635321373918603771408560000000000000)
      constant := (186523823622456117134662688441999071969782041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363782727067189338899/100000000000000000000)
  centralHi := (3637827270671893389/1000000000000000000)
  directionLo := (364917777335722475737/100000000000000000000)
  directionHi := (182458888667861237869/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree162.table
  base := (-2152246222289877819928718633434375450621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-97622571363775398518847217760000000000000)
      constant := (2205865276669770132574181705565959371845653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree162.table
  base := (-2152246234030112623414447216339951535749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-903422889373180182624734094720000000000000)
      constant := (20998375652490041323665836698730583053247813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364917777335722475737/100000000000000000000)
  centralHi := (182458888667861237869/50000000000000000000)
  directionLo := (45756163505389953759/12500000000000000000)
  directionHi := (366049308043119630073/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree163.table
  base := (-15678026776742975463565756299740104713/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-49117702312742039950227425360000000000000)
      constant := (1117431599544723034107685485497716433088576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree163.table
  base := (-250848429733603616045068663974984361871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-8181824373395869368641442296400000000000000)
      constant := (191462964438313645829412573807229470934553144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45756163505389953759/12500000000000000000)
  centralHi := (366049308043119630073/100000000000000000000)
  directionLo := (367177351728084452693/100000000000000000000)
  directionHi := (183588675864042226347/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree164.table
  base := (-464871525618532334722461766951485677709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-49424118943596380641031241840000000000000)
      constant := (1132024557218664208799428289182679200512074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree164.table
  base := (-464871527941936533570205245747293950923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-8232842742433117093660277740320000000000000)
      constant := (193956574303251342706612778346485137319306636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367177351728084452693/100000000000000000000)
  centralHi := (183588675864042226347/50000000000000000000)
  directionLo := (368301940431016735821/100000000000000000000)
  directionHi := (184150970215508367911/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree165.table
  base := (-17103422768504183647515038947161963557/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-49730535574450721331835058320000000000000)
      constant := (1146711511253782497490750533168493312755050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree165.table
  base := (-342068457023739453944352230908257362951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-920429012385596090964345909360000000000000)
      constant := (21829578938950921468600808779563898930670435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368301940431016735821/100000000000000000000)
  centralHi := (184150970215508367911/50000000000000000000)
  directionLo := (184711552852315491987/50000000000000000000)
  directionHi := (14776924228185239359/4000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree166.table
  base := (-1559355979527058046878409897318573800631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-100073904410610124045277749600000000000000)
      constant := (2322984923097330169593605276638769983395583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree166.table
  base := (-389838996720714799921774108963861720951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-8334879480507612543697948628160000000000000)
      constant := (198991872863813510079338962828469961616883132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184711552852315491987/50000000000000000000)
  centralHi := (14776924228185239359/4000000000000000000)
  directionLo := (370540878624285818179/100000000000000000000)
  directionHi := (18527043931214290909/5000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree167.table
  base := (-1406527239055936562159952483100148859801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-100686737672318805426885382560000000000000)
      constant := (2352734816006760724196943497418298957981393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree167.table
  base := (-1406527245599729384923823611071883057451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-8385897849544860268716784072080000000000000)
      constant := (201533561526835098232164282607062242306425283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370540878624285818179/100000000000000000000)
  centralHi := (18527043931214290909/5000000000000000000)
  directionLo := (371655289798033780239/100000000000000000000)
  directionHi := (4645691122475422253/1250000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree168.table
  base := (-1251856083574621947506685625361715496983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (110)
      previous := (44)
      next := (0)
      square := (1072458207990192417813357680000000000000)
      linear := (-101299570934027486808493015520000000000000)
      constant := (2382672701038893682533141850862467991521119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree168.table
  base := (-625928044697920803452953505476115884409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9652123871911731760320219120000000000000)
      linear := (-937435135398011999303957724000000000000000)
      constant := (22676808491519479224643055619590009398564466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell005.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (371655289798033780239/100000000000000000000)
  centralHi := (4645691122475422253/1250000000000000000)
  directionLo := (372766369376400731937/100000000000000000000)
  directionHi := (186383184688200365969/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree169.table
  base := (-273835635203744062878488176993068122697/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (55)
      previous := (22)
      next := (0)
      square := (536229103995096208906678840000000000000)
      linear := (-50956202097868084095050324240000000000000)
      constant := (1206399288999803005131016466642097046282242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree169.table
  base := (-1095342545993232098535157767431427271513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (86869114847205585842881972080000000000000)
      linear := (-8487934587619355718754454959920000000000000)
      constant := (206665017538615759904153289824406380737052129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell005.Kernel169
