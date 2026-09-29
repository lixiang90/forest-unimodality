import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell190.Parameters
import ForestUnimodality.BinomialMassData.Q1291_2376.Batch000_049
import ForestUnimodality.BinomialMassData.Q1291_2376.Batch050_099
import ForestUnimodality.BinomialMassData.Q2587_4752.Batch000_049
import ForestUnimodality.BinomialMassData.Q2587_4752.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree000.table
  base := (311898074244377369501535211/10000000000000000000000000)
  polynomial :=
    { denominator := 2376000000000000000000000000000000000000000
      center := (9037)
      previous := (0)
      next := (7595)
      square := (401174634470502431415894771600000000000000)
      linear := (-1441866685065420505829081324400000000000000)
      constant := (74106982440464062993564766133600000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree000.table
  base := (311898074244377369501535211/10000000000000000000000000)
  polynomial :=
    { denominator := 4752000000000000000000000000000000000000000
      center := (18109)
      previous := (0)
      next := (15155)
      square := (802349268941004862831789543200000000000000)
      linear := (-2883733370130841011658162648800000000000000)
      constant := (148213964880928125987129532267200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree001.table
  base := (195587317212565996602519297971404963770349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-309840843744324749983731772711500000000000000)
      constant := (7816614898057231480905793551965491449652762196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree001.table
  base := (195356507747098802827044334277276175891561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-619960280984809571100391250125500000000000000)
      constant := (15615784656090131360142443633133061024305514888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24901226410636671609/50000000000000000000)
  directionHi := (49802452821273343219/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree002.table
  base := (125086356370276139274356011149711071448119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-381773684452855116505665126897000000000000000)
      constant := (5240589664360779882149729928596897845052057276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree002.table
  base := (31200582677929471068572564551057238965903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-764104555898030375277185663199000000000000000)
      constant := (10460516822752331409082890701672246471354089696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24901226410636671609/50000000000000000000)
  centralHi := (49802452821273343219/100000000000000000000)
  directionLo := (35215652109645486327/50000000000000000000)
  directionHi := (14086260843858194531/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree003.table
  base := (81595684888215257986817499981813228493771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-151235508387128494342532827027500000000000000)
      constant := (1254186845283876959308980962951429019956599428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree003.table
  base := (4066330189518866255703616251717131782141/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52272000000000000000000000000000000000000000
      center := (199199)
      previous := (0)
      next := (166705)
      square := (8825841958351053491149684975200000000000000)
      linear := (-60549922054083411963598671751500000000000000)
      constant := (500459239263529776001236590474450200032148704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35215652109645486327/50000000000000000000)
  centralHi := (14086260843858194531/20000000000000000000)
  directionLo := (4313018931399870273/5000000000000000000)
  directionHi := (86260378627997405461/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree004.table
  base := (27079737528233934171234740257405247283431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-525639365869915849549531835268000000000000000)
      constant := (2953015242990257817920418764648130628999257848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree004.table
  base := (53925010588910650074243886284316476419447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-1052393105724471983630774489346000000000000000)
      constant := (5892073514858172059810943685187936283096000376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4313018931399870273/5000000000000000000)
  centralHi := (86260378627997405461/100000000000000000000)
  directionLo := (24901226410636671609/25000000000000000000)
  directionHi := (99604905642546686437/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree005.table
  base := (18183575523973540146888281589238435611441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-597572206578446216071465189453500000000000000)
      constant := (2560633571051546264706580143267288509421865928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree005.table
  base := (3616735741000073348108318699064652325461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156816000000000000000000000000000000000000000
      center := (597597)
      previous := (0)
      next := (500115)
      square := (26477525875053160473449054925600000000000000)
      linear := (-239307476127538557561513780483900000000000000)
      constant := (1022378594609753295726979964541475644069492176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24901226410636671609/25000000000000000000)
  centralHi := (99604905642546686437/100000000000000000000)
  directionLo := (11136166995459337991/10000000000000000000)
  directionHi := (111361669954593379911/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree006.table
  base := (764012971285798950322996659752981554769/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-223168349095658860864466181213000000000000000)
      constant := (812534921936427651234637834250737814647081344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree006.table
  base := (24276804076290953064659110369063840112649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-446893885183637863994787771831000000000000000)
      constant := (1623404159632850619183219421618040025184194264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11136166995459337991/10000000000000000000)
  centralHi := (111361669954593379911/100000000000000000000)
  directionLo := (121990597351152203877/100000000000000000000)
  directionHi := (60995298675576101939/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree007.table
  base := (16170728159182874764768556534237902897169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-741437887995506949115331897824500000000000000)
      constant := (2496404368429766647551455907215793995180613476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree007.table
  base := (16019772657160418268104103837041028867279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-1484825930464134396161157728566500000000000000)
      constant := (4991901654023405409772347948737353616425611832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121990597351152203877/100000000000000000000)
  centralHi := (60995298675576101939/50000000000000000000)
  directionLo := (26352980969223273269/20000000000000000000)
  directionHi := (65882452423058183173/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree008.table
  base := (10200804267723255641467457148365097930889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-813370728704037315637265252010000000000000000)
      constant := (2684762234006978614398546753448505299282572356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree008.table
  base := (2515987526264021670392949433605178830377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-1628970205377355200337952141640000000000000000)
      constant := (5372496496990788186031734722043459446928799264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26352980969223273269/20000000000000000000)
  centralHi := (65882452423058183173/50000000000000000000)
  directionLo := (35215652109645486327/25000000000000000000)
  directionHi := (140862608438581945309/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree009.table
  base := (1146758171986190206579393532048631394293/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26136000000000000000000000000000000000000000
      center := (99407)
      previous := (0)
      next := (83545)
      square := (4412920979175526745574842487600000000000000)
      linear := (-59020237960837845477279907079700000000000000)
      constant := (198074994886317986487850620600480265060620924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree009.table
  base := (5605953691383627856938946788537493568607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-591038160096858668171582184904500000000000000)
      constant := (1983001791605691974850457056477762806909112552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35215652109645486327/25000000000000000000)
  centralHi := (140862608438581945309/100000000000000000000)
  directionLo := (74703679231910014827/50000000000000000000)
  directionHi := (29881471692764005931/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree010.table
  base := (2277293953631730698091562893285355413483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-957236410121098048681131960381000000000000000)
      constant := (3336188622615981673942281124868984073630187532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree010.table
  base := (2154766437065610012056387967896275009899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-1917258755203796808691540967787000000000000000)
      constant := (6682928628206765354156505715933373630976160792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74703679231910014827/50000000000000000000)
  centralHi := (29881471692764005931/20000000000000000000)
  directionLo := (629956735913209479/400000000000000000)
  directionHi := (157489183978302369751/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree011.table
  base := (-118717600387365267807178867424985998329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (135555)
      previous := (0)
      next := (113925)
      square := (6017619517057536471238421574000000000000000)
      linear := (-93560840984511674109369574051500000000000000)
      constant := (342540881489100960025882246833333149607821776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree011.table
  base := (-297344790437915100537902711755871091549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (271635)
      previous := (0)
      next := (227325)
      square := (12035239034115072942476843148000000000000000)
      linear := (-187400275465183419351666852805500000000000000)
      constant := (686395064306818924132469100833005176718877456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629956735913209479/400000000000000000)
  centralHi := (157489183978302369751/100000000000000000000)
  directionLo := (82588024823770196851/50000000000000000000)
  directionHi := (165176049647540393703/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree012.table
  base := (-271681775886712260972221702498271866267/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26136000000000000000000000000000000000000000
      center := (99407)
      previous := (0)
      next := (83545)
      square := (4412920979175526745574842487600000000000000)
      linear := (-73406806102543918781666577916800000000000000)
      constant := (283919869229157806908872276155205166503245688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree012.table
  base := (-2835705306164646315612791069314228337793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-735182435010079472348376597978000000000000000)
      constant := (2845367018668765536608568248488153328163442152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82588024823770196851/50000000000000000000)
  centralHi := (165176049647540393703/100000000000000000000)
  directionLo := (172520757255994810921/100000000000000000000)
  directionHi := (86260378627997405461/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree013.table
  base := (-4574393362774609431089575868589322802127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-1173034932246689148246932022937500000000000000)
      constant := (4803800011824201954428299747252605438865413092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree013.table
  base := (-4693536161122048576202056429573470262311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-2349691579943459221221924207007500000000000000)
      constant := (9630373646947269234399819428069018968672719112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172520757255994810921/100000000000000000000)
  centralHi := (86260378627997405461/50000000000000000000)
  directionLo := (44891324322744313661/25000000000000000000)
  directionHi := (35913059458195450929/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree014.table
  base := (-766404819140526246225925421742617113233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-1244967772955219514768865377123000000000000000)
      constant := (5399676541453045996885130457656644509542507744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree014.table
  base := (-6251411491741489398162657414498204518683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-2493835854856680025398718620081000000000000000)
      constant := (10826637633637271422199167621169087280099103336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44891324322744313661/25000000000000000000)
  centralHi := (35913059458195450929/20000000000000000000)
  directionLo := (186343715478178121919/100000000000000000000)
  directionHi := (582324110869306631/312500000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree015.table
  base := (-7444449493678174903736221734565218081567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-438966871221249960430266243769500000000000000)
      constant := (2014729743106587985142910787155045480110082444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree015.table
  base := (-7566143240522089456208820256008476560447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-879326709923300276525171011051500000000000000)
      constant := (4040146168429610706453585424790759331616157208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186343715478178121919/100000000000000000000)
  centralHi := (582324110869306631/312500000000000000)
  directionLo := (48221017594268060609/25000000000000000000)
  directionHi := (192884070377072242437/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree016.table
  base := (-1069261586081757996810724784705030108321/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-1388833454372280247812732085494000000000000000)
      constant := (6735767308193010617949036140383391997067068128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree016.table
  base := (-8677602707949140127946262344127123737499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-2782124404683121633752307446228000000000000000)
      constant := (13508650032973500599549276298561680481990178408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48221017594268060609/25000000000000000000)
  centralHi := (192884070377072242437/100000000000000000000)
  directionLo := (199209811285093372873/100000000000000000000)
  directionHi := (99604905642546686437/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree017.table
  base := (-9489068584522970314253196062726112132011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-1460766295080810614334665439679500000000000000)
      constant := (7473277764969333249291388134224416749976640756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree017.table
  base := (-9614556081038503587301030481998067021097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-2926268679596342437929101859301500000000000000)
      constant := (14989016717499737141431534215996386186009826424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199209811285093372873/100000000000000000000)
  centralHi := (99604905642546686437/50000000000000000000)
  directionLo := (205340773396950251477/100000000000000000000)
  directionHi := (102670386698475125739/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree018.table
  base := (-10270784825596796525826063259212308332013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-510899711929780326952199597955000000000000000)
      constant := (2751960444787042673272033794718488554717254116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree018.table
  base := (-5199159073095616168662791688594250669199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-1023470984836521080701965424125000000000000000)
      constant := (5519955769698469340116064281444488829019629872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205340773396950251477/100000000000000000000)
  centralHi := (102670386698475125739/50000000000000000000)
  directionLo := (105646956328936458981/50000000000000000000)
  directionHi := (211293912657872917963/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree019.table
  base := (-10915501225527806617990030666319872371079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-1604631976497871347378532148050500000000000000)
      constant := (9082940566633971571322744020323876973564218884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree019.table
  base := (-5522541994230179291538278185425205964951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-3214557229422784046282690685448500000000000000)
      constant := (18219931983531675087165171519743876526400243984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105646956328936458981/50000000000000000000)
  centralHi := (211293912657872917963/100000000000000000000)
  directionLo := (43416771797676522549/20000000000000000000)
  directionHi := (108541929494191306373/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree020.table
  base := (-5717929186552920600460261929844384533061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-1676564817206401713900465502236000000000000000)
      constant := (9953959900144946992529998658462261497531753112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree020.table
  base := (-1156744871408393231464653272423391276393/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156816000000000000000000000000000000000000000
      center := (597597)
      previous := (0)
      next := (500115)
      square := (26477525875053160473449054925600000000000000)
      linear := (-671740300867200970091897019704400000000000000)
      constant := (3993644636743725063651858194775903473601155312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43416771797676522549/20000000000000000000)
  centralHi := (108541929494191306373/50000000000000000000)
  directionLo := (11136166995459337991/5000000000000000000)
  directionHi := (222723339909186759821/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree021.table
  base := (-5920948231457154027078570249808182528449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-582832552638310693474132952140500000000000000)
      constant := (3622848573035202121616264970632107091436456936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree021.table
  base := (-5987710187179290921995033243022028793601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-1167615259749741884878759837198500000000000000)
      constant := (7267985399456730893648939510963174385900888528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11136166995459337991/5000000000000000000)
  centralHi := (222723339909186759821/100000000000000000000)
  directionLo := (45644701969590425119/20000000000000000000)
  directionHi := (57055877461988031399/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree022.table
  base := (-12141749918469167734817399071037718164583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (135555)
      previous := (0)
      next := (113925)
      square := (6017619517057536471238421574000000000000000)
      linear := (-165493681693042040631302928237000000000000000)
      constant := (1075125374688766360963445235085696572461426188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree022.table
  base := (-3069277664680732939453248508018196552719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (271635)
      previous := (0)
      next := (227325)
      square := (12035239034115072942476843148000000000000000)
      linear := (-331544550378404223528461265879000000000000000)
      constant := (2156954091467352136239392998020072679888875872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45644701969590425119/20000000000000000000)
  centralHi := (57055877461988031399/25000000000000000000)
  directionLo := (11679710479538165551/5000000000000000000)
  directionHi := (233594209590763311021/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree023.table
  base := (-12342131580234045121385167146967492643121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-1892363339331992813466265564792500000000000000)
      constant := (12827196937359881860041225136268817668419084316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree023.table
  base := (-6239608224082508122771579667990509233243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-3791134329075667262989868337742500000000000000)
      constant := (25735314517986157986594145919586540929079765712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11679710479538165551/5000000000000000000)
  centralHi := (233594209590763311021/100000000000000000000)
  directionLo := (119422086589278592311/50000000000000000000)
  directionHi := (238844173178557184623/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree024.table
  base := (-6224338645813744771018092855473804484213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-654765393346841059996066306326000000000000000)
      constant := (4623592739616860408438991937785336646000609032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree024.table
  base := (-6293681304906007128634565291677912155317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-1311759534662962689055554250272000000000000000)
      constant := (9276657899774779432570247634230412175817269776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119422086589278592311/50000000000000000000)
  centralHi := (238844173178557184623/100000000000000000000)
  directionLo := (121990597351152203877/50000000000000000000)
  directionHi := (48796238940460881551/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree025.table
  base := (-12466195774043581015922443119713711088431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-2036229020749053546510132273163500000000000000)
      constant := (14956934444934994553354315065666774920489151076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree025.table
  base := (-12606350629016221550368475537611290072161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-4079422878902108871343457163889500000000000000)
      constant := (30010096075291911626238653594341114593022000312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121990597351152203877/50000000000000000000)
  centralHi := (48796238940460881551/20000000000000000000)
  directionLo := (249012264106366716091/100000000000000000000)
  directionHi := (62253066026591679023/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree026.table
  base := (-3099713203423860463219200624186106758387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-2108161861457583913032065627349000000000000000)
      constant := (16085502300130422597118555327308256482576784208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree026.table
  base := (-12540341912151940175167984147620584851557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-4223567153815329675520251576963000000000000000)
      constant := (32275355358337881697015855048224927682959118744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249012264106366716091/100000000000000000000)
  centralHi := (62253066026591679023/25000000000000000000)
  directionLo := (253943678760456817107/100000000000000000000)
  directionHi := (63485919690114204277/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree027.table
  base := (-6125154466002301618193852239408092426553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-726698234055371426517999660511500000000000000)
      constant := (5752112759118351882697405257185423846339610792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree027.table
  base := (-3098248702705311642974370581446223296433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-1455903809576183493232348663345500000000000000)
      constant := (11541821568143277633505602358067707906697708448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253943678760456817107/100000000000000000000)
  centralHi := (63485919690114204277/25000000000000000000)
  directionLo := (129390567941996108191/50000000000000000000)
  directionHi := (258781135883992216383/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree028.table
  base := (-1502977936142931579122847882021711359163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-2252027542874644646075932335720000000000000000)
      constant := (18469314596652695428037547035457266623002989984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree028.table
  base := (-12167568240029410441328985065234937686603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-4511855703641771283873840403110000000000000000)
      constant := (37060168588560032050043377520694309005868831976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129390567941996108191/50000000000000000000)
  centralHi := (258781135883992216383/100000000000000000000)
  directionLo := (26352980969223273269/10000000000000000000)
  directionHi := (263529809692232732691/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree029.table
  base := (-2930583540757451226507402678136603495827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-2323960383583175012597865689905500000000000000)
      constant := (19724316089298251923051086807359111636198393168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree029.table
  base := (-11867000783430386390173366242836913131117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-4655999978554992088050634816183500000000000000)
      constant := (39579236602261339872792580188761158940215378264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26352980969223273269/10000000000000000000)
  centralHi := (263529809692232732691/100000000000000000000)
  directionLo := (268194416242097699497/100000000000000000000)
  directionHi := (134097208121048849749/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree030.table
  base := (-11348518109935572664411666019150957008381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-798631074763901793039933014697000000000000000)
      constant := (7007079266685747023738055731118610293814477092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree030.table
  base := (-11493971560080092898110365228481594379757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-1600048084489404297409143076419000000000000000)
      constant := (14060819560388939970869895357963092549290671048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268194416242097699497/100000000000000000000)
  centralHi := (134097208121048849749/50000000000000000000)
  directionLo := (136389634146491055379/50000000000000000000)
  directionHi := (272779268292982110759/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree031.table
  base := (-1363104917493154273636023991229849714611/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-2467826065000235745641732398276500000000000000)
      constant := (22359983129878310986000062032684631024307122848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree031.table
  base := (-690684210319838364600262953315282046343/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-4944288528381433696404223642330500000000000000)
      constant := (44869641408803222563136152204176176469965408896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136389634146491055379/50000000000000000000)
  centralHi := (272779268292982110759/100000000000000000000)
  directionLo := (34661040249976150431/12500000000000000000)
  directionHi := (277288321999809203449/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree032.table
  base := (-10393585621433081005653757293476031559541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-2539758905708766112163665752462000000000000000)
      constant := (23740462389090115942439361848194565658739754636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree032.table
  base := (-527010969226617192381744346595194568901/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156816000000000000000000000000000000000000000
      center := (597597)
      previous := (0)
      next := (500115)
      square := (26477525875053160473449054925600000000000000)
      linear := (-1017686560658930900116203611080800000000000000)
      constant := (9528121027571888864755587832363855936966441568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34661040249976150431/12500000000000000000)
  centralHi := (277288321999809203449/100000000000000000000)
  directionLo := (35215652109645486327/12500000000000000000)
  directionHi := (281725216877163890617/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree033.table
  base := (-9816897372514370233061434313660736359059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11880000000000000000000000000000000000000000
      center := (45185)
      previous := (0)
      next := (37975)
      square := (2005873172352512157079473858000000000000000)
      linear := (-79142174133857469051078760807500000000000000)
      constant := (762502777719420163649716072642902295205437908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree033.table
  base := (-9963931932236546211507371977083133959221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23760000000000000000000000000000000000000000
      center := (90545)
      previous := (0)
      next := (75775)
      square := (4011746344705024314158947716000000000000000)
      linear := (-158562941763875009235085226317500000000000000)
      constant := (1530157022332433318204805061771341098712890904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35215652109645486327/12500000000000000000)
  centralHi := (281725216877163890617/100000000000000000000)
  directionLo := (71523327545764827139/25000000000000000000)
  directionHi := (286093310183059308557/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree034.table
  base := (-4588395192100857390482037856608140258649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-2683624587125826845207532460833000000000000000)
      constant := (26626291929759700883493837241602693938599849208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree034.table
  base := (-2331026261785318628018189267759509941647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-5376721353121096108934606881551000000000000000)
      constant := (53433212818924834522840215202219111877981368096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71523327545764827139/25000000000000000000)
  centralHi := (286093310183059308557/100000000000000000000)
  directionLo := (5807914132922949619/2000000000000000000)
  directionHi := (290395706646147480951/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree035.table
  base := (-4237586886569917560382598771397829596591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-2755557427834357211729465815018500000000000000)
      constant := (28131488339137682770238078938105520226990492872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree035.table
  base := (-8622652342852293491205971878109011905119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-5520865628034316913111401294624500000000000000)
      constant := (56454548341107448588141954167992244219543429448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5807914132922949619/2000000000000000000)
  centralHi := (290395706646147480951/100000000000000000000)
  directionLo := (29463528428470766139/10000000000000000000)
  directionHi := (294635284284707661391/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree036.table
  base := (-964233028912909551464380029256509246623/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-942496756180962526083799723068000000000000000)
      constant := (9892703223760880330750036353613907497321045088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree036.table
  base := (-1965348793321265851000299787941224729079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-1888336634315845905762731902566000000000000000)
      constant := (19853015164933446096327453084813222601923165024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29463528428470766139/10000000000000000000)
  centralHi := (294635284284707661391/100000000000000000000)
  directionLo := (298814716927640059309/100000000000000000000)
  directionHi := (29881471692764005931/10000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree037.table
  base := (-6894597392585420242848805599310635122159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-2899423109251417944773332523389500000000000000)
      constant := (31266087882403419417713391557960907110670878564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree037.table
  base := (-7042073930872121564912969022976043858253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-5809154177860758521464990120771500000000000000)
      constant := (62746567819313653239609679663052259978162098776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298814716927640059309/100000000000000000000)
  centralHi := (29881471692764005931/10000000000000000000)
  directionLo := (302936493938186351007/100000000000000000000)
  directionHi := (9466765435568323469/3125000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree038.table
  base := (-1203807389811307363677512745282140801947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78408000000000000000000000000000000000000000
      center := (298221)
      previous := (0)
      next := (250635)
      square := (13238762937526580236724527462800000000000000)
      linear := (-594271189991989662259053175515000000000000000)
      constant := (6579071549823219034708328719547883952000469812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree038.table
  base := (-3083178553742866960109349063480516623363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-5953298452773979325641784533845000000000000000)
      constant := (66016984491536672811708195710295801805190707792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302936493938186351007/100000000000000000000)
  centralHi := (9466765435568323469/3125000000000000000)
  directionLo := (1199230224818981267/390625000000000000)
  directionHi := (307002937553659204353/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree039.table
  base := (-1272195501748212991197502490281905873789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1014429596889492892605733077253500000000000000)
      constant := (11521952193352738367478126162613827966165301392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree039.table
  base := (-1047169721196296415580788148968906706693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52272000000000000000000000000000000000000000
      center := (199199)
      previous := (0)
      next := (166705)
      square := (8825841958351053491149684975200000000000000)
      linear := (-406496181845813341987905263127900000000000000)
      constant := (4624677983510286437503931737073058029313871752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1199230224818981267/390625000000000000)
  centralHi := (307002937553659204353/100000000000000000000)
  directionLo := (311016218184182688059/100000000000000000000)
  directionHi := (15550810909209134403/5000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree040.table
  base := (-4105373063325248844163377075288032033691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-3115221631377009044339132585946000000000000000)
      constant := (36277523981588100860904344274680407992151178036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree040.table
  base := (-4252093681177663384182859767693055239361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-6241587002600420933995373359992000000000000000)
      constant := (72806002442326731433840060616489722924792182712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311016218184182688059/100000000000000000000)
  centralHi := (15550810909209134403/5000000000000000000)
  directionLo := (314978367956604739501/100000000000000000000)
  directionHi := (157489183978302369751/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree041.table
  base := (-153514844939029616363540813073344076863/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78408000000000000000000000000000000000000000
      center := (298221)
      previous := (0)
      next := (250635)
      square := (13238762937526580236724527462800000000000000)
      linear := (-637430894417107882172213188026300000000000000)
      constant := (7606060333190827287711628475780496725242651792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree041.table
  base := (-643316761001006840142002232488645009937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156816000000000000000000000000000000000000000
      center := (597597)
      previous := (0)
      next := (500115)
      square := (26477525875053160473449054925600000000000000)
      linear := (-1277146255502728347634433554613100000000000000)
      constant := (15264873123444566136149367793444358447060859704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314978367956604739501/100000000000000000000)
  centralHi := (157489183978302369751/50000000000000000000)
  directionLo := (6377825854870025989/2000000000000000000)
  directionHi := (318891292743501299451/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree042.table
  base := (-1984990618701716834911125062876598060649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1086362437598023259127666431439000000000000000)
      constant := (13274711097626153784920925580541203616543438868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree042.table
  base := (-2130760685519893856747717931127230646501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-2176625184142287514116320728713000000000000000)
      constant := (26641715411965771995156836962116246199823049864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6377825854870025989/2000000000000000000)
  centralHi := (318891292743501299451/100000000000000000000)
  directionLo := (322756782879363515487/100000000000000000000)
  directionHi := (10086149464980109859/3125000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree043.table
  base := (-850845021871028070023903659726586236077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-3331020153502600143904932648502500000000000000)
      constant := (41658964337485610176340203277378860163200837292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree043.table
  base := (-996019619018961085808148044462790050359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-6674019827340083346525756599212500000000000000)
      constant := (83608234895958154225553854307622527182731451528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322756782879363515487/100000000000000000000)
  centralHi := (10086149464980109859/3125000000000000000)
  directionLo := (163288261367475340397/50000000000000000000)
  directionHi := (65315304546990136159/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree044.table
  base := (82698140433642842561988131617956653469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (135555)
      previous := (0)
      next := (113925)
      square := (6017619517057536471238421574000000000000000)
      linear := (-309359363110102773675169636608000000000000000)
      constant := (3957703816277378946715639264914845590051854064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree044.table
  base := (93143842363877044088701413567755835841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (271635)
      previous := (0)
      next := (227325)
      square := (12035239034115072942476843148000000000000000)
      linear := (-619833100204845831882050092026000000000000000)
      constant := (7943047782958699859549133109101571927195749296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163288261367475340397/50000000000000000000)
  centralHi := (65315304546990136159/20000000000000000000)
  directionLo := (82588024823770196851/25000000000000000000)
  directionHi := (66070419859016157481/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree045.table
  base := (1558615854018111974975456897846039223543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1158295278306553625649599785624500000000000000)
      constant := (15150471668749540824883934220364645790573259924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree045.table
  base := (353712673662409553613579107797853997103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-2320769459055508318293115141786500000000000000)
      constant := (30406971876513254671494524151964290723273136032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82588024823770196851/25000000000000000000)
  centralHi := (66070419859016157481/20000000000000000000)
  directionLo := (33408500986378013973/10000000000000000000)
  directionHi := (334085009863780139731/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree046.table
  base := (2831357546361739748120894729334948775393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-3546818675628191243470732711059000000000000000)
      constant := (47408933735510918010618852950389472331790507172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree046.table
  base := (672099495571444705158522353802022353569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-7106452652079745759056139838433000000000000000)
      constant := (95150305256777587678748141304086698374794552608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33408500986378013973/10000000000000000000)
  centralHi := (334085009863780139731/100000000000000000000)
  directionLo := (337776669002903796533/100000000000000000000)
  directionHi := (168888334501451898267/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree047.table
  base := (2073893742065675895841965707193638794427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-3618751516336721609992666065244500000000000000)
      constant := (49407249939855779651759977664034670080593432216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree047.table
  base := (801139082068653337724505714183803151301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156816000000000000000000000000000000000000000
      center := (597597)
      previous := (0)
      next := (500115)
      square := (26477525875053160473449054925600000000000000)
      linear := (-1450119385398593312646586850301300000000000000)
      constant := (19832319545604461404372368248725001762487208808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337776669002903796533/100000000000000000000)
  centralHi := (168888334501451898267/50000000000000000000)
  directionLo := (341428414795418554403/100000000000000000000)
  directionHi := (85357103698854638601/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree048.table
  base := (688338883133178533140656578201821692623/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1230228119015083992171533139810000000000000000)
      constant := (17148772262032048924748891174379531247033578912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree048.table
  base := (5365544533321502743520642117420273157639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-2464913733968729122469909554860000000000000000)
      constant := (34418233025186370357186664042316896259248052904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341428414795418554403/100000000000000000000)
  centralHi := (85357103698854638601/25000000000000000000)
  directionLo := (345041514511989621843/100000000000000000000)
  directionHi := (86260378627997405461/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree049.table
  base := (6906967809938293225630470037385255774229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-3762617197753782343036532773615500000000000000)
      constant := (53526088778804455978416845247783182817372873716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree049.table
  base := (6766781168955841369612415757493037377157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-7538885476819408171586523077653500000000000000)
      constant := (107429518018184993494405532705047404699668126056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345041514511989621843/100000000000000000000)
  centralHi := (86260378627997405461/25000000000000000000)
  directionLo := (10894286554653543829/3125000000000000000)
  directionHi := (348617169748913402529/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree050.table
  base := (2086857518203185629880138087617166137319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-3834550038462312709558466127801000000000000000)
      constant := (55646521709749385112629660094913398524989816304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree050.table
  base := (513017131755917265809562029205386627079/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-7683029751732628975763317490727000000000000000)
      constant := (111685965860052795142534674628389037774496163712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10894286554653543829/3125000000000000000)
  centralHi := (348617169748913402529/100000000000000000000)
  directionLo := (35215652109645486327/10000000000000000000)
  directionHi := (352156521096454863271/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree051.table
  base := (9827001865179553523800432843296460152561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1302160959723614358693466493995500000000000000)
      constant := (19269190870599139537724406489592291891273667148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree051.table
  base := (4844461968776589441693689103924698211161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-2609058008881949926646703967933500000000000000)
      constant := (38674652132791173327374395041456523699893807792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35215652109645486327/10000000000000000000)
  centralHi := (352156521096454863271/100000000000000000000)
  directionLo := (44457581548625689729/12500000000000000000)
  directionHi := (355660652389005517833/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree052.table
  base := (5672308886873174322189205123664616358337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-3978415719879373442602332836172000000000000000)
      constant := (60009199716485842108848752312841795239424487496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree052.table
  base := (5603830977953643668935416523054880431387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-7971318301559070584116906316874000000000000000)
      constant := (120443405838405910165908972224316624129728383792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44457581548625689729/12500000000000000000)
  centralHi := (355660652389005517833/100000000000000000000)
  directionLo := (44891324322744313661/12500000000000000000)
  directionHi := (359130594581954509289/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree053.table
  base := (6449620977958416941931557106404100346527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-4050348560587903809124266190357500000000000000)
      constant := (62251362414641510489782527343916213949970489016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree053.table
  base := (12763449166433067178190794161763151221001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-8115462576472291388293700729947500000000000000)
      constant := (124944232714494835442460665302615790785936246408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44891324322744313661/12500000000000000000)
  centralHi := (359130594581954509289/100000000000000000000)
  directionLo := (362567329294578513497/100000000000000000000)
  directionHi := (181283664647289256749/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree054.table
  base := (14489867200352196851598556537279626902607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1374093800432144725215399848181000000000000000)
      constant := (21511340406517032318337089066837045164363268276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree054.table
  base := (14355275334716668997605455326330902371283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-2753202283795170730823498381007000000000000000)
      constant := (43175452605393458235831484272168171964375852488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (362567329294578513497/100000000000000000000)
  centralHi := (181283664647289256749/50000000000000000000)
  directionLo := (22873237003341038227/6250000000000000000)
  directionHi := (365971792053456611633/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree055.table
  base := (16115514042631484547757350009388326818509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (135555)
      previous := (0)
      next := (113925)
      square := (6017619517057536471238421574000000000000000)
      linear := (-381292203818633140197102990793500000000000000)
      constant := (6077921612026494769375430817672053746781166076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree055.table
  base := (499442440658119677668807232963592254063/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (271635)
      previous := (0)
      next := (227325)
      square := (12035239034115072942476843148000000000000000)
      linear := (-763977375118066636058844505099500000000000000)
      constant := (12199064010782118777002322821039985413782754048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22873237003341038227/6250000000000000000)
  centralHi := (365971792053456611633/100000000000000000000)
  directionLo := (184672437633390249439/50000000000000000000)
  directionHi := (369344875266780498879/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree056.table
  base := (17775229928085027693922035364780649908311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-4266147082713494908690066252914000000000000000)
      constant := (69220674608909277299746864652560860599005424444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree056.table
  base := (17643142139842271430020936004610449059933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-8547895401211953800824083969168000000000000000)
      constant := (138934196716592396218405242930584496089891226664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184672437633390249439/50000000000000000000)
  centralHi := (369344875266780498879/100000000000000000000)
  directionLo := (372687430956356243839/100000000000000000000)
  directionHi := (582324110869306631/156250000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree057.table
  base := (9734044207743963416559293604776359261553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1446026641140675091737333202366500000000000000)
      constant := (23874865176400940168850478161157778675659949208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree057.table
  base := (19337298359598191043294190166560236024311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-2897346558708391535000292794080500000000000000)
      constant := (47919920920647997675085202195558265203731392296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372687430956356243839/100000000000000000000)
  centralHi := (582324110869306631/156250000000000000)
  directionLo := (1880001366354981931/500000000000000000)
  directionHi := (376000273270996386201/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree058.table
  base := (10596594208282924175114733370672867355719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-4410012764130555641733932961285000000000000000)
      constant := (74068865166907365108496380495922343183627215352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree058.table
  base := (2632965392351906707772784620162605149571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-8836183951038395409177672795315000000000000000)
      constant := (148666331403502557815635455233991238856540503744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1880001366354981931/500000000000000000)
  centralHi := (376000273270996386201/100000000000000000000)
  directionLo := (379284180802309650773/100000000000000000000)
  directionHi := (189642090401154825387/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree059.table
  base := (22949653467258447361648678080592912661783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-4481945604839086008255866315470500000000000000)
      constant := (76553449161125889344764813227445345797992540732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree059.table
  base := (22821537593446128153894985625909710646123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-8980328225951616213354467208388500000000000000)
      constant := (153653833729727707450084974027034594217341212184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379284180802309650773/100000000000000000000)
  centralHi := (189642090401154825387/50000000000000000000)
  directionLo := (382539898721550709079/100000000000000000000)
  directionHi := (9563497468038767727/2500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree060.table
  base := (1546039439216609226260319030476295880119/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1517959481849205458259266556552000000000000000)
      constant := (26359438029625437915520356019126727752982321472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree060.table
  base := (24609886872893287938112864010499910903871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-3041490833621612339177087207154000000000000000)
      constant := (52907400904497930354831491787212175671383572456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382539898721550709079/100000000000000000000)
  centralHi := (9563497468038767727/2500000000000000000)
  directionLo := (385768140754144484873/100000000000000000000)
  directionHi := (192884070377072242437/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree061.table
  base := (207447592239187622441306835596625745021/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-4625811286256146741299733023841500000000000000)
      constant := (81643427438651064075582306156405236060598820352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree061.table
  base := (6606984870458356486266781801269896466083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-9268616775778057821708056034535500000000000000)
      constant := (163871373158915498798137528350574395793450543456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385768140754144484873/100000000000000000000)
  centralHi := (192884070377072242437/50000000000000000000)
  directionLo := (77793918201341314929/20000000000000000000)
  directionHi := (194484795503353287323/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree062.table
  base := (14199414556438129331925435092423253411599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-4697744126964677107821666378027000000000000000)
      constant := (84248757584903519679950347150605347453496654392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree062.table
  base := (565497732514485512821321590056281397629/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156816000000000000000000000000000000000000000
      center := (597597)
      previous := (0)
      next := (500115)
      square := (26477525875053160473449054925600000000000000)
      linear := (-1882552210138255725176970089521800000000000000)
      constant := (33820256330006072123328086903373341618252946320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77793918201341314929/20000000000000000000)
  centralHi := (194484795503353287323/50000000000000000000)
  directionLo := (392144905659808036957/100000000000000000000)
  directionHi := (196072452829904018479/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree063.table
  base := (6054491644841354957918092387968570759023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26136000000000000000000000000000000000000000
      center := (99407)
      previous := (0)
      next := (83545)
      square := (4412920979175526745574842487600000000000000)
      linear := (-317978464511547164956239982147500000000000000)
      constant := (5792951584226055739341005839435042032678912564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree063.table
  base := (30149941578211955172986395603517997775427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-3185635108534833143353881620227500000000000000)
      constant := (58137288833732807117221166723458843264858560072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392144905659808036957/100000000000000000000)
  centralHi := (196072452829904018479/50000000000000000000)
  directionLo := (79058942907669819807/20000000000000000000)
  directionHi := (98823678634587274759/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree064.table
  base := (8043353944940339563845565076222480610213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-4841609808381737840865533086398000000000000000)
      constant := (89579946047314398654115857619280904519371161808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree064.table
  base := (32052339068953110427791634995647065623647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-9701049600517720234238439273756000000000000000)
      constant := (179803067709102599293911764083474695121418913976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79058942907669819807/20000000000000000000)
  centralHi := (98823678634587274759/25000000000000000000)
  directionLo := (199209811285093372873/50000000000000000000)
  directionHi := (398419622570186745747/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree065.table
  base := (2131309949398259699421398442612777402891/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-4913542649090268207387466440583500000000000000)
      constant := (92305745324208470828814206802541592454847020224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree065.table
  base := (33981334690600296961187127325704872372511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-9845193875430941038415233686829500000000000000)
      constant := (185274826906251596019396969743084258257983842488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199209811285093372873/50000000000000000000)
  centralHi := (398419622570186745747/100000000000000000000)
  directionLo := (100380052785645993891/25000000000000000000)
  directionHi := (80304042228516795113/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree066.table
  base := (1802718303352318102505706928006370502493/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2376000000000000000000000000000000000000000
      center := (9037)
      previous := (0)
      next := (7595)
      square := (401174634470502431415894771600000000000000)
      linear := (-30215002968477567114602422998600000000000000)
      constant := (576191777415363507539455342669011272627846736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree066.table
  base := (35936204323884643689924965940401414434211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23760000000000000000000000000000000000000000
      center := (90545)
      previous := (0)
      next := (75775)
      square := (4011746344705024314158947716000000000000000)
      linear := (-302707216677095813411879639391000000000000000)
      constant := (5782639009572781148006782281343456260695685336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100380052785645993891/25000000000000000000)
  centralHi := (80304042228516795113/20000000000000000000)
  directionLo := (202298519682547587167/50000000000000000000)
  directionHi := (80919407873019034867/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree067.table
  base := (38032933666551582412102242867742505007941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-5057408330507328940431333148954500000000000000)
      constant := (97877612344948239530399250182998258416331318964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree067.table
  base := (37916243579877392344075060744291158905633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-10133482425257382646768822512976500000000000000)
      constant := (196459793708326018809963622203020396812472872264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202298519682547587167/50000000000000000000)
  centralHi := (80919407873019034867/20000000000000000000)
  directionLo := (407650645246656676127/100000000000000000000)
  directionHi := (12739082663958021129/3125000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree068.table
  base := (20017989176643015938519718966717213502713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-5129341171215859306953266503140000000000000000)
      constant := (100723625737198120832377007858583863276320720904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree068.table
  base := (39920767258629628244119688550189785204967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-10277626700170603450945616926050000000000000000)
      constant := (202172892358366724294424764859482530678351052536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407650645246656676127/100000000000000000000)
  centralHi := (12739082663958021129/3125000000000000000)
  directionLo := (82136309358780100591/20000000000000000000)
  directionHi := (102670386698475125739/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree069.table
  base := (42062835076725417301745439593296782006689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1733758003974796557825066619108500000000000000)
      constant := (34536552459214622753852721568927296097263411852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree069.table
  base := (2097455441174192168002417500261453502407/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52272000000000000000000000000000000000000000
      center := (199199)
      previous := (0)
      next := (166705)
      square := (8825841958351053491149684975200000000000000)
      linear := (-694784731672254950341494089274900000000000000)
      constant := (13864422066947843496532678668030717769955637408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82136309358780100591/20000000000000000000)
  centralHi := (102670386698475125739/25000000000000000000)
  directionLo := (413690243037040753533/100000000000000000000)
  directionHi := (206845121518520376767/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree070.table
  base := (22056428431907657585313033824736395020699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-5273206852632920039997133211511000000000000000)
      constant := (106535681902353856198437366487115556260782967192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree070.table
  base := (22000309945213467916037315252869417303511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-10565915249997045059299205752197000000000000000)
      constant := (213840058807385103980037734489710533043867380976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (413690243037040753533/100000000000000000000)
  centralHi := (206845121518520376767/50000000000000000000)
  directionLo := (416677214989086009713/100000000000000000000)
  directionHi := (208338607494543004857/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree071.table
  base := (11546353581435056758062909153983493601371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-5345139693341450406519066565696500000000000000)
      constant := (109501674636768961841724763809790606782592594736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree071.table
  base := (23037334865957895283551460734256457025651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-10710059524910265863476000165270500000000000000)
      constant := (219794026313783878322347987789439801189934487216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416677214989086009713/100000000000000000000)
  centralHi := (208338607494543004857/50000000000000000000)
  directionLo := (419642926543598682911/100000000000000000000)
  directionHi := (13113841454487458841/3125000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree072.table
  base := (24139947589275661987919541647413223679107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1805690844683326924346999973294000000000000000)
      constant := (37502537192303085100934005821732792014077140552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree072.table
  base := (24085322397328393139734653056899108605593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-3618067933274495555884264859448000000000000000)
      constant := (75276061805309109739051534510927230205031557296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419642926543598682911/100000000000000000000)
  centralHi := (13113841454487458841/3125000000000000000)
  directionLo := (16903513012629833437/4000000000000000000)
  directionHi := (211293912657872917963/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree073.table
  base := (12598925944294163865380480522433978029913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-5489005374758511139562933274067500000000000000)
      constant := (115553469371105335832704201752017037948738837008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree073.table
  base := (50287948230861848688960286155088823036757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-10998348074736707471829588991417500000000000000)
      constant := (231942489316174089336294601746087845061666042856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16903513012629833437/4000000000000000000)
  centralHi := (211293912657872917963/50000000000000000000)
  directionLo := (425512343430959091133/100000000000000000000)
  directionHi := (212756171715479545567/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree074.table
  base := (52532260662372208182555584318978060844681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-5560938215467041506084866628253000000000000000)
      constant := (118639225302237001133753702599649840897354873924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree074.table
  base := (10485199888507581357680007377941683188839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156816000000000000000000000000000000000000000
      center := (597597)
      previous := (0)
      next := (500115)
      square := (26477525875053160473449054925600000000000000)
      linear := (-2228498469929985655201276680898200000000000000)
      constant := (47627378498199343593647468073214163995470488312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425512343430959091133/100000000000000000000)
  centralHi := (212756171715479545567/50000000000000000000)
  directionLo := (107104224566284508317/25000000000000000000)
  directionHi := (428416898265138033269/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree075.table
  base := (54689002120201160406098779802247903697821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1877623685391857290868933327479500000000000000)
      constant := (40588285756821024015578736689289369355523124828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree075.table
  base := (10916846727679057695823782563533131679557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52272000000000000000000000000000000000000000
      center := (199199)
      previous := (0)
      next := (166705)
      square := (8825841958351053491149684975200000000000000)
      linear := (-752442441637543272012211854504300000000000000)
      constant := (16294090043749318300204688655224486304576901752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107104224566284508317/25000000000000000000)
  centralHi := (428416898265138033269/100000000000000000000)
  directionLo := (53912736642498378413/12500000000000000000)
  directionHi := (86260378627997405461/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree076.table
  base := (56865379753653163677038943225939806960031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-5704803896884102239128733336624000000000000000)
      constant := (124930343776427154870817491146117244192061055324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree076.table
  base := (56762101402984872075274065421691578437281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-11430780899476369884359972230638000000000000000)
      constant := (250765820733336724207650004066435243282110328648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53912736642498378413/12500000000000000000)
  centralHi := (86260378627997405461/20000000000000000000)
  directionLo := (43416771797676522549/10000000000000000000)
  directionHi := (434167717976765225491/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree077.table
  base := (29530430033018209825796204863648581528129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (135555)
      previous := (0)
      next := (113925)
      square := (6017619517057536471238421574000000000000000)
      linear := (-525157885235693873240969699164500000000000000)
      constant := (11648696718629540394884350094283430839132503512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree077.table
  base := (58959068277694598924590603034675761153833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (271635)
      previous := (0)
      next := (227325)
      square := (12035239034115072942476843148000000000000000)
      linear := (-1052265924944508244412433331246500000000000000)
      constant := (23381841892405155707924435761312715700504521624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43416771797676522549/10000000000000000000)
  centralHi := (434167717976765225491/100000000000000000000)
  directionLo := (218507374955724951573/50000000000000000000)
  directionHi := (437014749911449903147/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree078.table
  base := (30637462027896714357062939915834283089147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-1949556526100387657390866681665000000000000000)
      constant := (43793599103006460083512000622755119822817945992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree078.table
  base := (61174614353253961108346162145164131080057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-3906356483100937164237853685595000000000000000)
      constant := (87904876713517886085578504891391697229908369752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218507374955724951573/50000000000000000000)
  centralHi := (437014749911449903147/100000000000000000000)
  directionLo := (439843353874060782441/100000000000000000000)
  directionHi := (219921676937030391221/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree079.table
  base := (63507066822407136528666207458784517706793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-5920602419009693338694533399180500000000000000)
      constant := (134665724194590591993054452420629219482177112772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree079.table
  base := (63408233873410864700229246736958990220519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-11863213724216032296890355469858500000000000000)
      constant := (270308889050291346435775936186002871130210453752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439843353874060782441/100000000000000000000)
  centralHi := (219921676937030391221/50000000000000000000)
  directionLo := (442653883134664726841/100000000000000000000)
  directionHi := (221326941567332363421/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree080.table
  base := (65756797183078240299579163919624000368567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-5992535259718223705216466753366000000000000000)
      constant := (137990425305308115704483158392684939310449300668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree080.table
  base := (65659434849459271033841833894885244746737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-12007357999129253101067149882932000000000000000)
      constant := (276982998969819314244535121729190162270102154696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442653883134664726841/100000000000000000000)
  centralHi := (221326941567332363421/50000000000000000000)
  directionLo := (11136166995459337991/2500000000000000000)
  directionHi := (445446679818373519641/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree081.table
  base := (1062869332810421690406885664840228785527/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-2021489366808918023912800035850500000000000000)
      constant := (47118293969337787117884817691640298775233077504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree081.table
  base := (2717109547412343178347367473243417462571/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52272000000000000000000000000000000000000000
      center := (199199)
      previous := (0)
      next := (166705)
      square := (8825841958351053491149684975200000000000000)
      linear := (-810100151602831593682929619733700000000000000)
      constant := (18915794824891685991147245862778309169008778280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11136166995459337991/2500000000000000000)
  centralHi := (445446679818373519641/100000000000000000000)
  directionLo := (112055518847865022241/25000000000000000000)
  directionHi := (89644415078292017793/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree082.table
  base := (70307122317004188105329860398575947607011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-6136400941135284438260333461737000000000000000)
      constant := (144759075778500753534157346188059396449985259244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree082.table
  base := (70212679812797105161239369806244822262723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-12295646548955694709420738709079000000000000000)
      constant := (290570622756690851920938398926008106523975584984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112055518847865022241/25000000000000000000)
  centralHi := (89644415078292017793/20000000000000000000)
  directionLo := (112745097780137121869/25000000000000000000)
  directionHi := (450980391120548487477/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree083.table
  base := (72606800008086552529954790339410076990779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-6208333781843814804782266815922500000000000000)
      constant := (148202989187686377761764045005108513908346499916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree083.table
  base := (72513805336962437192255139695054185701421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-12439790823868915513597533122152500000000000000)
      constant := (297484064609177787688015284803221324217477017768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112745097780137121869/25000000000000000000)
  centralHi := (450980391120548487477/100000000000000000000)
  directionLo := (453721938506678389853/100000000000000000000)
  directionHi := (226860969253339194927/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree084.table
  base := (7492223043288111438612925562738751989621/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26136000000000000000000000000000000000000000
      center := (99407)
      previous := (0)
      next := (83545)
      square := (4412920979175526745574842487600000000000000)
      linear := (-418684441503489678086946678007200000000000000)
      constant := (10112440325876889386354255645653440022000734456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree084.table
  base := (14966134938198220436137548864040536624319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52272000000000000000000000000000000000000000
      center := (199199)
      previous := (0)
      next := (166705)
      square := (8825841958351053491149684975200000000000000)
      linear := (-838929006585475754518288502348400000000000000)
      constant := (20298480892458225756557503136839713465213201384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453721938506678389853/100000000000000000000)
  centralHi := (226860969253339194927/50000000000000000000)
  directionLo := (45644701969590425119/10000000000000000000)
  directionHi := (456447019695904251191/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree085.table
  base := (38626492801736195194588047015935707589493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-6352199463260875537826133524293500000000000000)
      constant := (155209906101063404028114231759048768210676967144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree085.table
  base := (38581429650289470165311393115485009932667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-12728079373695357121951121948299500000000000000)
      constant := (311550035486123607340702129598815162942601108272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45644701969590425119/10000000000000000000)
  centralHi := (456447019695904251191/100000000000000000000)
  directionLo := (114788981966990292397/25000000000000000000)
  directionHi := (459155927867961169589/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree086.table
  base := (15919729831898869704727259949733146225253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78408000000000000000000000000000000000000000
      center := (298221)
      previous := (0)
      next := (250635)
      square := (13238762937526580236724527462800000000000000)
      linear := (-1284826460793881180869613375695800000000000000)
      constant := (31754575300684955508206236272860463264614818612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree086.table
  base := (496937139109012665896153908930834174873/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156816000000000000000000000000000000000000000
      center := (597597)
      previous := (0)
      next := (500115)
      square := (26477525875053160473449054925600000000000000)
      linear := (-2574444729721715585225583272274600000000000000)
      constant := (63740499643596744933179414572176675571470149888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114788981966990292397/25000000000000000000)
  centralHi := (459155927867961169589/100000000000000000000)
  directionLo := (461848947604412667867/100000000000000000000)
  directionHi := (115462236901103166967/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree087.table
  base := (16391763210439428046113786859382402439557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26136000000000000000000000000000000000000000
      center := (99407)
      previous := (0)
      next := (83545)
      square := (4412920979175526745574842487600000000000000)
      linear := (-433071009645195751391333348844300000000000000)
      constant := (10825033347713751484743997529890577985080130876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree087.table
  base := (81871518001725923579370623627690052216857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-4338789307840599576768236924815500000000000000)
      constant := (108644856594438890536288204392013354079739774552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461848947604412667867/100000000000000000000)
  centralHi := (115462236901103166967/25000000000000000000)
  directionLo := (464526355237588941437/100000000000000000000)
  directionHi := (232263177618794470719/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree088.table
  base := (42166546118553026115157024083150777031451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (135555)
      previous := (0)
      next := (113925)
      square := (6017619517057536471238421574000000000000000)
      linear := (-597090725944224239762903053350000000000000000)
      constant := (15092523799071663778098617077328698738680182728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree088.table
  base := (42123596006534300899589933457062681248621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (271635)
      previous := (0)
      next := (227325)
      square := (12035239034115072942476843148000000000000000)
      linear := (-1196410199857729048589227744320000000000000000)
      constant := (30295110840779082013603509426016885583880340976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464526355237588941437/100000000000000000000)
  centralHi := (232263177618794470719/50000000000000000000)
  directionLo := (467188419181526622041/100000000000000000000)
  directionHi := (233594209590763311021/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree089.table
  base := (86721094375037271239075793498252169863209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-6639930826094997003913866941035500000000000000)
      constant := (169699646197241503188827723651625509317317245636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree089.table
  base := (86636580510079553624726132160973167858823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-13304656473348240338658299600593500000000000000)
      constant := (340637416522212149370036459808357724770474593784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467188419181526622041/100000000000000000000)
  centralHi := (233594209590763311021/50000000000000000000)
  directionLo := (234917700123015948389/50000000000000000000)
  directionHi := (469835400246031896779/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree090.table
  base := (44561224770620939966718540404459992569489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-2237287888934509123478600098407000000000000000)
      constant := (57807046272641340201880508925087841365796164504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree090.table
  base := (89039310158004512428089938768355523483349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (995995)
      previous := (0)
      next := (833525)
      square := (44129209791755267455748424876000000000000000)
      linear := (-4482933582753820380945031337889000000000000000)
      constant := (116036044110604000244098756969226927461760809464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234917700123015948389/50000000000000000000)
  centralHi := (469835400246031896779/100000000000000000000)
  directionLo := (118116887983726777313/25000000000000000000)
  directionHi := (472467551934907109253/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree091.table
  base := (22884198735614012204180043641581524725797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-6783796507512057736957733649406500000000000000)
      constant := (177182225428888738637938443277734029631400582352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree091.table
  base := (91455017784351788890505059870750624902531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-13592945023174681947011888426740500000000000000)
      constant := (355658338201740727860312214668083080622357650648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118116887983726777313/25000000000000000000)
  centralHi := (472467551934907109253/100000000000000000000)
  directionLo := (118771280182326512133/25000000000000000000)
  directionHi := (475085120729306048533/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree092.table
  base := (5872736102602605250777763873594831626761/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-6855729348220588103479667003592000000000000000)
      constant := (180982892193592015853384917806142088465528611904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree092.table
  base := (11735418762782823793320855494824921472039/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-13737089298087902751188682839814000000000000000)
      constant := (363288006431482306538775243174003109542237071296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118771280182326512133/25000000000000000000)
  centralHi := (475085120729306048533/100000000000000000000)
  directionLo := (95537669271422873849/20000000000000000000)
  directionHi := (238844173178557184623/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree093.table
  base := (3856122171608314326115511426627726141609/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26136000000000000000000000000000000000000000
      center := (99407)
      previous := (0)
      next := (83545)
      square := (4412920979175526745574842487600000000000000)
      linear := (-461844145928607898000106690518500000000000000)
      constant := (12321541710093046235697119941971174376092732060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree093.table
  base := (9632396344141381255397533925066235011557/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52272000000000000000000000000000000000000000
      center := (199199)
      previous := (0)
      next := (166705)
      square := (8825841958351053491149684975200000000000000)
      linear := (-925415571533408237024365150192500000000000000)
      constant := (24733140671635602854017006787078496611524107504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95537669271422873849/20000000000000000000)
  centralHi := (238844173178557184623/50000000000000000000)
  directionLo := (60034682756148551853/12500000000000000000)
  directionHi := (19211098481967536593/4000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree094.table
  base := (12356786358438651134525334420667826103531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-6999595029637648836523533711963000000000000000)
      constant := (188702912707354390905960990796841516636502634592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree094.table
  base := (19755304697249541408351917374555282629251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156816000000000000000000000000000000000000000
      center := (597597)
      previous := (0)
      next := (500115)
      square := (26477525875053160473449054925600000000000000)
      linear := (-2805075569582868871908454333192200000000000000)
      constant := (75757124583576336946527979924240143100394312408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60034682756148551853/12500000000000000000)
  centralHi := (19211098481967536593/4000000000000000000)
  directionLo := (482852694783227626183/100000000000000000000)
  directionHi := (60356586847903453273/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree095.table
  base := (101317162427423154417061698294926731916123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-7071527870346179203045467066148500000000000000)
      constant := (192622240622280318245847205542156338848039686092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree095.table
  base := (101240705021328545887902612243550122996801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-14169522122827565163719066079034500000000000000)
      constant := (386653519462033347751020129676095168668933172808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482852694783227626183/100000000000000000000)
  centralHi := (60356586847903453273/12500000000000000000)
  directionLo := (242707132758001125681/50000000000000000000)
  directionHi := (485414265516002251363/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree096.table
  base := (51895676425906626131679507052009180267493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (497035)
      previous := (0)
      next := (417725)
      square := (22064604895877633727874212438000000000000000)
      linear := (-2381153570351569856522466806778000000000000000)
      constant := (65527032334359351495464415333471311935471197048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree096.table
  base := (10371619168363194218139774321030381644711/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52272000000000000000000000000000000000000000
      center := (199199)
      previous := (0)
      next := (166705)
      square := (8825841958351053491149684975200000000000000)
      linear := (-954244426516052397859724032807200000000000000)
      constant := (26306718326773134382431838721380900109332333392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242707132758001125681/50000000000000000000)
  centralHi := (485414265516002251363/100000000000000000000)
  directionLo := (487962389404608815509/100000000000000000000)
  directionHi := (48796238940460881551/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree097.table
  base := (106276554610691349739802762915704009652733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-7215393551763239936089333774519500000000000000)
      constant := (200579469793341944082276170096999791244425744532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree097.table
  base := (53101337860788924647224876563251126598723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-14457810672654006772072654905181500000000000000)
      constant := (402627365106386800393020084924154179293705345968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell190.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487962389404608815509/100000000000000000000)
  centralHi := (48796238940460881551/10000000000000000000)
  directionLo := (245248638008690196477/50000000000000000000)
  directionHi := (98099455203476078591/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree098.table
  base := (108772468528896311962166729416504705138099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1491105)
      previous := (0)
      next := (1253175)
      square := (66193814687632901183622637314000000000000000)
      linear := (-7287326392471770302611267128705000000000000000)
      constant := (204617347264208969901494773286764275460234033196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree098.table
  base := (54349928880311732316352139052310792683697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (2987985)
      previous := (0)
      next := (2500575)
      square := (132387629375265802367245274628000000000000000)
      linear := (-14601954947567227576249449318255000000000000000)
      constant := (410733266603043549654829505022724231765486628752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell190.Kernel098
