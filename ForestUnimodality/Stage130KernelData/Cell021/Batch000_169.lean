import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell021.Parameters
import ForestUnimodality.BinomialMassData.Q7_17.Batch000_049
import ForestUnimodality.BinomialMassData.Q7_17.Batch050_099
import ForestUnimodality.BinomialMassData.Q7_17.Batch100_149
import ForestUnimodality.BinomialMassData.Q7_17.Batch150_199
import ForestUnimodality.BinomialMassData.Q64_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q64_153.Batch050_099
import ForestUnimodality.BinomialMassData.Q64_153.Batch100_149
import ForestUnimodality.BinomialMassData.Q64_153.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel000
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
  base := (20343289891584587382169502329/1000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (490)
      previous := (343)
      next := (0)
      square := (5622202188870505587536818920000000000000)
      linear := (20464660690555119548772467600000000000000)
      constant := (3458359281569379854968815395930000000000000) }

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
  base := (20343289891584587382169502329/1000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4361)
      previous := (3136)
      next := (0)
      square := (50599819699834550287831370280000000000000)
      linear := (184181946214996075938952208400000000000000)
      constant := (31125233534124418694719338563370000000000000) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel001
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
  base := (16180464195352420721754549067789015976761/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (269188401095249954103616484320000000000000)
      constant := (37282185765835890564430951590768204938271432) }

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
  base := (32068735153119431322569326721999600580973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (7234353616438525727272424163120000000000000)
      constant := (997451686749824432798170508148171533333329276) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel002
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
  base := (42262191247254767178194313641705673298731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (190477570451062875878101019440000000000000)
      constant := (24205861975305402525616864415465879166666518) }

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
  base := (83117197252397247825493036921833864859669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (5075427975912251581658285697840000000000000)
      constant := (642511220468271860121597524663949647499997207) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel003
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
  base := (56892243589801068108927052920543356115351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (111766739806875797652585554560000000000000)
      constant := (16157947062085668406138269247597029917336439) }

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
  base := (6950703815206663787235462999522162789903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (972167445128659145348049077520000000000000)
      constant := (142055650143975653065934189155817163332301624) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel004
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
  base := (19785614176831050897654471684273514985329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (33055909162688719427070089680000000000000)
      constant := (11122357231112479152692118248550091661520162) }

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
  base := (38507475067218179483304993203732158980759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (757576694859703290430008767280000000000000)
      constant := (291981608591114327678787547337042036526862477) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel005
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
  base := (1421487963255026559239409926241542929177/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-45654921481498358798445375200000000000000)
      constant := (7905066578819116642592788488676118130643060) }

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
  base := (27586223614249116549024051879401056390311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-1401348945666570855184129698000000000000000)
      constant := (206897728680236074452738014926966443013596733) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel006
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
  base := (10515032126747846349356378140616192723989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-124365752125685437023960840080000000000000)
      constant := (5801558976796209101609834018716159394465642) }

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
  base := (20369063454516938269322197186387802301453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-1186758195397615000266089387760000000000000)
      constant := (50539984378993294269790362687234673786079253) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel007
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
  base := (15924169636072440626223853807135557443771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-203076582769872515249476304960000000000000)
      constant := (4393370030721739419305072380622176101249819) }

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
  base := (15402827725015573404933673188778475083683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-5719200226719119146412406628560000000000000)
      constant := (114809220929309378868696073173318441077978449) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel008
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
  base := (12248700162517268376638866285812475343193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-281787413414059593474991769840000000000000)
      constant := (3430984293255104190971225002359805374182777) }

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
  base := (2957491953714453833104496732569781606289/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-7878125867245393292026545093840000000000000)
      constant := (89774080246471689348006803723848023495492268) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel009
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
  base := (9485841545421903488152478777363505804263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-360498244058246671700507234720000000000000)
      constant := (2764753435335312675146555866298053177432007) }

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
  base := (914118990930890828684190947463332382453/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-3345683835923889145880227853040000000000000)
      constant := (24180170484030505004509764774561275267602530) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel010
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
  base := (7322398197432620880138172921528227543273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-439209074702433749926022699600000000000000)
      constant := (2304163932217138323530001166321657760005897) }

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
  base := (1757803273771246270515372245508542232247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-12195977148297941583254822024400000000000000)
      constant := (60726407579814840211782288766812620152893364) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel011
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
  base := (1113332725767283334311241702806148462733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-517919905346620828151538164480000000000000)
      constant := (1993812608373523014501075983394884528649185) }

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
  base := (1328656705654383343860261800928787749899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-14354902788824215728868960489680000000000000)
      constant := (52885010111358563133179589678109323249847588) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel012
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
  base := (4099353054838748065569334718367048625949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-596630735990807906377053629360000000000000)
      constant := (1799226160998843879773814825768077052899261) }

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
  base := (1938382937201053669701327949965793783937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-5504609476450163291494366318320000000000000)
      constant := (16040528784845164328376874334282059264040274) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel013
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
  base := (177787908088898794232464795948381463829/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-675341566634994984602569094240000000000000)
      constant := (1698481065694120190909822516425315888745296) }

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
  base := (2644991107596761348281558170904625559063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-18672754069876764020097237420240000000000000)
      constant := (45869333077749928050573290652048793237368589) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel014
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
  base := (438205434619391028613536021350703544893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-754052397279182062828084559120000000000000)
      constant := (1677242253681634058162463986921413297896308) }

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
  base := (785932666905449972857457272498741978237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-20831679710403038165711375885520000000000000)
      constant := (45758097899990051983508356228535367312366622) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel015
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
  base := (49403925782396079598968349441557130181/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-832763227923369141053600024000000000000000)
      constant := (1725817858679942749008839878817760169956944) }

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
  base := (125053455313591030681152548957842540969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-7663535116976437437108504783600000000000000)
      constant := (15845746166969734949761541027196742245301845) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel016
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
  base := (-66013766881582214642768548726723766649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-911474058567556219279115488880000000000000)
      constant := (1837403803863850649921126843657976831438439) }

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
  base := (-217444002482778051871750660470111583251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-25149530991455586456939652816080000000000000)
      constant := (51030087638556835351670756891071719315892447) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel017
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
  base := (-416900245181675675571725485974555281679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (490)
      previous := (343)
      next := (0)
      square := (5622202188870505587536818920000000000000)
      linear := (-58246169953631958676742997280000000000000)
      constant := (118060674084591963978458187356865120422914) }

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
  base := (-194579342271076108857820499096802528573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (13083)
      previous := (9408)
      next := (0)
      square := (151799459099503650863494110840000000000000)
      linear := (-1606379801881285917797281840080000000000000)
      constant := (3300405612105827672323924940812838196924965) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel018
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
  base := (-1525940018987195407848827000474025346617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1068895719855930375730146418640000000000000)
      constant := (2230931496356175858558977913023006674827687) }

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
  base := (-826893342691727741568832932323130667649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-9822460757502711582722643248880000000000000)
      constant := (20889532066509268210280646685415074266889902) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel019
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
  base := (-2152671574438736439136304700196108616721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1147606550500117453955661883520000000000000)
      constant := (2506144779551043288981622096483324609767631) }

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
  base := (-567535623855850998519518562121099580757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-31626307913034408893782068211920000000000000)
      constant := (70636937081350539972146482029796239885412516) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel020
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
  base := (-2722267932914538399415158653590427846771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1226317381144304532181177348400000000000000)
      constant := (2830280476701858696077441381112366352283181) }

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
  base := (-2830109237897035004996095586669341840587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-33785233553560683039396206677200000000000000)
      constant := (79948361863887901389127702681219125617899639) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel021
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
  base := (-405195888263080770229742982855531974293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1305028211788491610406692813280000000000000)
      constant := (3201362402430199111505347371278010075434584) }

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
  base := (-668089246229917774913016802216630160847/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-11981386398028985728336781714160000000000000)
      constant := (30183375862030659454352473239812724758184765) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel022
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
  base := (-3716319507807286471033999417523117715757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1383739042432678688632208278160000000000000)
      constant := (3617728687148377006067461070095818980146227) }

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
  base := (-152274119792036839342395153771969665067/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-38103084834613231330624483607760000000000000)
      constant := (102397760896369039357749561910413017587054975) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel023
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
  base := (-4151422299026287729207720986300817992823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1462449873076865766857723743040000000000000)
      constant := (4077964051326285971526712129319063600074153) }

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
  base := (-4234190735611975086268951589180006840391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-40262010475139505476238622073040000000000000)
      constant := (115453329798363440258491186117308406624429027) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel024
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
  base := (-568885453503407805625041680992035273179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1541160703721052845083239207920000000000000)
      constant := (4580852340115163992885786558986414448410152) }

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
  base := (-925327807155822513333438771680878014383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-14140312038555259873950920179440000000000000)
      constant := (43228073670732324395375404362130181422949085) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel025
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
  base := (-2459471181436225761819384156789003791329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1619871534365239923308754672800000000000000)
      constant := (5125341920645023448534101152375955808611838) }

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
  base := (-2493905672969039113386624498772116163769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-44579861756192053767466899003600000000000000)
      constant := (145062238782558921450503168792162355148220986) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel026
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
  base := (-5258158782133787372609774858557324620541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1698582365009427001534270137680000000000000)
      constant := (5710519472408575872707985368916933184663651) }

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
  base := (-2660421727901469347181707824192851763483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-46738787396718327913081037468880000000000000)
      constant := (161562914542310423155083594932766355379084302) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel027
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
  base := (-5571485677074735858486513061286535411353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1777293195653614079759785602560000000000000)
      constant := (6335589438730679629967795974848191266118983) }

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
  base := (-2814231786374668905024461160579129439173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-16299237679081534019565058644720000000000000)
      constant := (59721653363099776470526025147627368657422054) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel028
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
  base := (-5861325736791419611421100592503794751363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1856004026297801157985301067440000000000000)
      constant := (6999857442462555280199570963326403316856093) }

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
  base := (-2956524682533992343015418220073451059623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-51056638677770876204309314399440000000000000)
      constant := (197849822477853237017481681210813722763523462) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel029
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
  base := (-6129778941862012917202249914529050854143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-1934714856941988236210816532320000000000000)
      constant := (7702716589217110454810372432741104303152673) }

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
  base := (-6176675379614708780736551701016347844953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-53215564318297150349923452864720000000000000)
      constant := (217601314018856108708685459229289437765831741) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel030
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
  base := (-318934119791874874095630142212239490513/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2013425687586175314436331997200000000000000)
      constant := (8443635956068111440742316898013255744834860) }

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
  base := (-6421153073881987436191283306161918751271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-18458163319607808165179197110000000000000000)
      constant := (79468433303164714595122218424672849327944129) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel031
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
  base := (-1321928846374544015402891535821570499031/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2092136518230362392661847462080000000000000)
      constant := (9222150792533807521042800151177830628900205) }

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
  base := (-415504061860407715258729200118796731491/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-57533415599349698641151729795280000000000000)
      constant := (260249431575347370363541875055888465666811632) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel032
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
  base := (-170601818501882097045552938945565390421/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2170847348874549470887362926960000000000000)
      constant := (10037854102773101376889988585149264086733240) }

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
  base := (-685879415349474862542698599053987057821/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-59692341239875972786765868260560000000000000)
      constant := (283122917262770940945155378429097389878227370) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel033
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
  base := (-7023201549317579000845991384929298633199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2249558179518736549112878391840000000000000)
      constant := (10890389368041872268080374026515432695005489) }

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
  base := (-3527274751977054255277405853380808547453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-20617088960134082310793335575280000000000000)
      constant := (102338774540542039351901132935673033936149494) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel034
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
  base := (-901013936756985929024842246428041376251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (490)
      previous := (343)
      next := (0)
      square := (5622202188870505587536818920000000000000)
      linear := (-136957000597819036902258462160000000000000)
      constant := (692908483951897335127023416405786372829864) }

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
  base := (-7236387965992973269366061915699449805117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (13083)
      previous := (9408)
      next := (0)
      square := (151799459099503650863494110840000000000000)
      linear := (-3765305442407560063411420305360000000000000)
      constant := (19524788439254180544700097084053952539451297) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel035
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
  base := (-737974965985419753521100602848242063811/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2406979840807110705563909321600000000000000)
      constant := (12704744972466256028280503264768580435586210) }

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
  base := (-7405233658427021064525843088116070946959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-66169118161454795223608283656400000000000000)
      constant := (357830945900737057854474307503430298400878923) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel036
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
  base := (-3769473002820819931591168727056338935191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2485690671451297783789424786480000000000000)
      constant := (13666051745763357531540121975601436095459602) }

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
  base := (-1512378927253620804155289298746643280439/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-22776014600660356456407474040560000000000000)
      constant := (128246215222872200570019090417639904137890805) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel037
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
  base := (-7686427891162779395964318284798805557651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2564401502095484862014940251360000000000000)
      constant := (14663154340107379927761145846853145193838861) }

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
  base := (-1926769374956769362036293543761619216743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-70486969442507343514836560586960000000000000)
      constant := (412638989168734096842507503839792341007017484) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel038
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
  base := (-977854098188264522990812615655378395631/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2643112332739671940240455716240000000000000)
      constant := (15695868526931746702386774233564765149301128) }

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
  base := (-7841400151869485494441297125677893952949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-72645895083033617660450699052240000000000000)
      constant := (441527154905810002266469263700815393485138953) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel039
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
  base := (-3974359695729680851915381536551880480407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2721823163383859018465971181120000000000000)
      constant := (16764032841130809238632824481113013082324754) }

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
  base := (-7965402943061943137827790581632019673353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-24934940241186630602021612505840000000000000)
      constant := (157132975507864240435778951689815116829608847) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel040
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
  base := (-4032288693646165325428908326047809994259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2800533994028046096691486646000000000000000)
      constant := (17867505765684591089592070843544365823318298) }

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
  base := (-504972400782004148793686585158889013799/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-76963746364086165951678975982800000000000000)
      constant := (502250616799425526298427314560083024405222448) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel041
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
  base := (-4085417980112689417345989597821136570359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2879244824672233174917002110880000000000000)
      constant := (19006163265486409426265745553699383062332498) }

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
  base := (-255758743823212501693509058619166508797/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-79122672004612440097293114448080000000000000)
      constant := (534079001205023078722375444369748599419424288) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel042
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
  base := (-8267871282881781799423127000188193910799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-2957955655316420253142517575760000000000000)
      constant := (20179896626648137616411874361905611959779089) }

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
  base := (-1034991062709640452979794468604288198701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-27093865881712904747635750971120000000000000)
      constant := (188960419940352923269881856616641971161429592) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel043
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
  base := (-8356013064490468436665569989781512845171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3036666485960607331368033040640000000000000)
      constant := (21388610563202615210353921700113142787745581) }

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
  base := (-1673364111053369718815629186543627030683/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-83440523285664988388521391378640000000000000)
      constant := (600654926550334214391084857093080391397902755) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel044
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
  base := (-210888757295849649511785687033339913993/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3115377316604794409593548505520000000000000)
      constant := (22632221557969686057450825085734590594240920) }

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
  base := (-105565404433188533600104455207356035593/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-85599448926191262534135529843920000000000000)
      constant := (635397844709638542903369787296080068341425680) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel045
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
  base := (-340269450417646056101513852889610993209/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3194088147248981487819063970400000000000000)
      constant := (23910656408541522052882109079872560574064975) }

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
  base := (-851540561475142882698124734267483071797/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-29252791522239178893249889436400000000000000)
      constant := (223702709399177374583729558189702765302560030) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel046
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
  base := (-4284896491969544314475026190224538487333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3272798977893168566044579435280000000000000)
      constant := (25223850952979884382009143406690216754321526) }

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
  base := (-4288775862831683763542134662674225433681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-89917300207243810825363806774480000000000000)
      constant := (707784127537006286467511141768226037881974314) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel047
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
  base := (-8624915058519684984805521404747345451177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3351509808537355644270094900160000000000000)
      constant := (26571748952985317607878757574788017164609847) }

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
  base := (-8631855558280415661136858032598998088237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-92076225847770084970977945239760000000000000)
      constant := (745424400180510130893727132376110017917486689) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel048
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
  base := (-867227304991105085317529719542742721191/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3430220639181542722495610365040000000000000)
      constant := (27954301115062397829783419925881473535758010) }

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
  base := (-2169619698053848032290345562666530983027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-31411717162765453038864027901680000000000000)
      constant := (261342561514008277050987367584577411652587092) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel049
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
  base := (-4356008230942934267832311933459455400809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3508931469825729800721125829920000000000000)
      constant := (29371464232620819862559214910900434778332398) }

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
  base := (-1743512565214799263886382940081958823261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-96394077128822633262206222170320000000000000)
      constant := (823592877288230114918513463460222376510472085) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel050
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
  base := (-69954210704212572211954009248733299371/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3587642300469916878946641294800000000000000)
      constant := (30823200434065260426376345855889509560222625) }

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
  base := (-8749231322484412311176508199040363983121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-98553002769348907407820360635600000000000000)
      constant := (864119013479638261820164718362888039839706837) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel051
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
  base := (-8769167542066898209712597481713776121287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (490)
      previous := (343)
      next := (0)
      square := (5622202188870505587536818920000000000000)
      linear := (-215667831242006115127773927040000000000000)
      constant := (1900557442575098184014401166930865805938121) }

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
  base := (-8773592433731203979389697305361474938903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4361)
      previous := (3136)
      next := (0)
      square := (50599819699834550287831370280000000000000)
      linear := (-1974743694311278069675186256880000000000000)
      constant := (17756965670666133724339872829399694334347841) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel052
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
  base := (-549174422282778148457835149571083917681/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3745063961758291035397672224560000000000000)
      constant := (33830263404507459050852989686943307964643056) }

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
  base := (-8790740748080374078436367360835525460457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-102870854050401455699048637566160000000000000)
      constant := (948050846388994169789710650950280394832054029) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel053
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
  base := (-1759446846885832705284486392771472266587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3823774792402478113623187689440000000000000)
      constant := (35385535571131978833807878328005222574781785) }

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
  base := (-8800758991849504922503291830642251288407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-105029779690927729844662776031440000000000000)
      constant := (991455159521246216567696734966778513196560179) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel054
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
  base := (-4400287667325500027781592316122475064051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3902485623046665191848703154320000000000000)
      constant := (36975270666936809345659825392321209412978522) }

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
  base := (-8803719517876630412292984950570694144571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-35729568443818001330092304832240000000000000)
      constant := (345272541343844593916036682589005624529970829) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel055
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
  base := (-1759376373512178784261750669910673206933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-3981196453690852270074218619200000000000000)
      constant := (38599449094724750672384663456979077215981815) }

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
  base := (-4399842803597015144092183654492129292893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-109347630971980278135891052962000000000000000)
      constant := (1081137746137961986516773871999995830255111842) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel056
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
  base := (-43931066372279235406411021007943310519/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4059907284335039348299734084080000000000000)
      constant := (40258053675960969248229326423180876652001800) }

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
  base := (-8788712607348839457250371821836971314857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-111506556612506552281505191427280000000000000)
      constant := (1127415093963620537193798112122526112830170829) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel057
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
  base := (-350744866451371453038192090954520876667/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4138618114979226426525249548960000000000000)
      constant := (41951069352026369730747618681213586666080925) }

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
  base := (-8770848927870439235531558257849407653387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-37888494084344275475706443297520000000000000)
      constant := (391549763256317223790039426753093690693540413) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel058
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
  base := (-8744152704670758132826254823373929836437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4217328945623413504750765013840000000000000)
      constant := (43678482922376458187942124833804934277269707) }

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
  base := (-8746136910811951571511995405944922428547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-115824407893559100572733468357840000000000000)
      constant := (1222840003158914878481713187650291770290047759) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel059
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
  base := (-8712846446015497882846333128561489811817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4296039776267600582976280478720000000000000)
      constant := (45440282815046566594718360981485729444384887) }

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
  base := (-1089326699005425225884063072218674214747/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-117983333534085374718347606823120000000000000)
      constant := (1271986945142616350785886785600941480818633272) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel060
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
  base := (-8674737987495589650396615953375955342211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4374750606911787661201795943600000000000000)
      constant := (47236458885507517653580050861474348906101021) }

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
  base := (-8676311367006704218630101348082819223343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-40047419724870549621320581762800000000000000)
      constant := (440696620979474277061252367193636587200084857) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel061
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
  base := (-2157464525521593398986033180000108535727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4453461437555974739427311408480000000000000)
      constant := (49067002240369438058152222970759874532699588) }

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
  base := (-8631258572922112182016485516342505830297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-122301184815137923009575883753680000000000000)
      constant := (1373148535431004682583709382055499427006192509) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel062
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
  base := (-4289116884112352860533363382369937061879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4532172268200161817652826873360000000000000)
      constant := (50931905082864076423978880585150176378233938) }

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
  base := (-8579479997931171123687154977468382789223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-124460110455664197155190022218960000000000000)
      constant := (1425162769198493426023111376950494209095692931) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel063
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
  base := (-425994431921177856430734565733941083043/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4610883098844348895878342338240000000000000)
      constant := (52831160577415184102336288962017820540011460) }

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
  base := (-2130249331586355018901178387593652618367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-42206345365396823766934720228080000000000000)
      constant := (492710798346068707478519629555635638158509732) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel064
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
  base := (-1690968689999481778521708846068348964467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4689593929488535974103857803120000000000000)
      constant := (54764762730938876062832518439671235746345185) }

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
  base := (-4227914764009705873402514454148664230323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-128777961736716745446418299149520000000000000)
      constant := (1532057264928367697032445041750475946021579262) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel065
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
  base := (-2095779096262482603702981302765782524107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4768304760132723052329373268000000000000000)
      constant := (56732706288807191848357877145002755402132308) }

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
  base := (-8383993198860341157114488152940643331167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-130936887377243019592032437614800000000000000)
      constant := (1586937249371114307074064537646604160086903899) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel066
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
  base := (-2076180846497993617284507764473527242129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4847015590776910130554888732880000000000000)
      constant := (58734986643663395007251451202508602508098876) }

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
  base := (-4152751429303284651825995266992047124153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-44365271005923097912548858693360000000000000)
      constant := (547590745022975840566632868503347370860156094) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel067
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
  base := (-1643935686416720015258688958602807050207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-4925726421421097208780404197760000000000000)
      constant := (60771599755501328482529038118778943812450885) }

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
  base := (-4110185605618877653249809402015051597739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-135254738658295567883260714545360000000000000)
      constant := (1699562122892654060795946753622233104765685166) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel068
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
  base := (-2031998445453791041495655039152752819979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (490)
      previous := (343)
      next := (0)
      square := (5622202188870505587536818920000000000000)
      linear := (-294378661886193193353289391920000000000000)
      constant := (3696620122448075242441532397817612808241428) }

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
  base := (-4064304686353155373612382828727802900077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (13083)
      previous := (9408)
      next := (0)
      square := (151799459099503650863494110840000000000000)
      linear := (-8083156723460108354639697235920000000000000)
      constant := (103370989770853956281837565693467876937729314) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel069
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
  base := (-1003710023168461155345024602406235335141/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5083148082709471365231435127520000000000000)
      constant := (64947810515214711420366198270076783905154008) }

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
  base := (-8030227070091345089415809014117069798869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-46524196646449372058162997158640000000000000)
      constant := (605335422934706272847131360700521501453141731) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel070
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
  base := (-7924747070711361069176159980688802180203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5161858913353658443456950592400000000000000)
      constant := (67087402331592901693732534917580936169921333) }

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
  base := (-247663525492549481463193133514729247607/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-141731515579874390320103129941200000000000000)
      constant := (1875660384569445584295946336357906165789522528) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel071
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
  base := (-1562640541400812201900389766044405859513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5240569743997845521682466057280000000000000)
      constant := (69261315140982562227330614779705833533003715) }

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
  base := (-156272681193672784030297487428599521589/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-143890441220400664465717268406480000000000000)
      constant := (1936269115268408068898235406049651896652051650) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel072
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
  base := (-769505434743133660245143230912995165367/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5319280574642032599907981522160000000000000)
      constant := (71469546847207289782472129732421443972089370) }

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
  base := (-1539087464523682173451635476961311487637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-48683122286975646203777135623920000000000000)
      constant := (665944136673169660727239522314278144103280815) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel073
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
  base := (-3785154177339094144841530406874362542239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5397991405286219678133496987040000000000000)
      constant := (73712095611451119231517787611186618450585858) }

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
  base := (-7570648312604152348521058530429235735171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-148208292501453212756945545337040000000000000)
      constant := (2060350224282925828617704452230740673558460687) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel074
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
  base := (-1859742577698847112161099335730090760813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5476702235930406756359012451920000000000000)
      constant := (75988959820501377357385242709336015080500172) }

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
  base := (-371963601341187408464602223355730939089/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-150367218141979486902559683802320000000000000)
      constant := (2123822519065640560265510588394624629645770660) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel075
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
  base := (-7301045113513394300338546424755153090939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5555413066574593834584527916800000000000000)
      constant := (78300138058913962023204597818245760756718629) }

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
  base := (-228166026271577483307902326254786557463/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-50842047927501920349391274089200000000000000)
      constant := (729416420075434448139576854701161605249239584) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel076
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
  base := (-7156537060660573884641679153570688345439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5634123897218780912810043381680000000000000)
      constant := (80645629084616474865451639491658071068168129) }

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
  base := (-1431354917151272073761400071012379525843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-154685069423032035193787960732880000000000000)
      constant := (2253630417867313814816265644138572012799235355) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel077
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
  base := (-3502724962077659527293525304364024638507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5712834727862967991035558846560000000000000)
      constant := (83025431807524500638599757011637593758942954) }

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
  base := (-3502830308922903657526591079829367487821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-156843995063558309339402099198160000000000000)
      constant := (2319965965803174050000994804627062890985065474) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel078
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
  base := (-6847787014860064578782239419429722768293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5791545558507155069261074311440000000000000)
      constant := (85439545270798795694521360154344810119963323) }

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
  base := (-1369594775328270424285642425721506153227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-53000973568028194495005412554480000000000000)
      constant := (795751960365180418068713518483251812477282865) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel079
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
  base := (-6683551239426106721504578406201603761661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5870256389151342147486589776320000000000000)
      constant := (87887968634417135412840299734647736512879971) }

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
  base := (-835464617224269044141286169091494332467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-161161846344610857630630376128720000000000000)
      constant := (2455500143646609444950461349100952557790079992) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel080
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
  base := (-6512745150118647348765875331489916675081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-5948967219795529225712105241200000000000000)
      constant := (90370701160774876454279163309199414080901591) }

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
  base := (-3256446029248708482540889396813337972629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-163320771985137131776244514594000000000000000)
      constant := (2524698735843500012758697971785331047599151826) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel081
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
  base := (-6335370988489252200826871073731993044211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6027678050439716303937620706080000000000000)
      constant := (92887742202063616319902596764131454010223021) }

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
  base := (-253420048693725064502748758619442205829/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-55159899208554468640619551019760000000000000)
      constant := (864950547415753244192551154992210770565969275) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel082
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
  base := (-24029026264280374907451458083421500271/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6106388881083903382163136170960000000000000)
      constant := (95439091189208295001809417892516143723950336) }

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
  base := (-6151546149179465925909766739925877390957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-167638623266189680067472791524560000000000000)
      constant := (2665958849320868219736951349105638378718362529) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel083
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
  base := (-5960926085855906719266106328756395480993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6185099711728090460388651635840000000000000)
      constant := (98024747622170220655266828739749401705993023) }

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
  base := (-745128546949543128330231537496136959897/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-169797548906715954213086929989840000000000000)
      constant := (2738020345191359405558238957954221146415389672) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel084
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
  base := (-46110868766865460561299161169904530599/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6263810542372277538614167100720000000000000)
      constant := (100644711061447285757681911011377198832111125) }

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
  base := (-5763949231587647940701815369697176844769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-57318824849080742786233689485040000000000000)
      constant := (937012039813925337662377043718457643026755831) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel085
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
  base := (-5560229590742202103099514231099354620897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (490)
      previous := (343)
      next := (0)
      square := (5622202188870505587536818920000000000000)
      linear := (-373089492530380271578804856800000000000000)
      constant := (6076410654154322724772875069071310971444751) }

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
  base := (-5560309888869988154760064191665036946147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (13083)
      previous := (9408)
      next := (0)
      square := (151799459099503650863494110840000000000000)
      linear := (-10242082363986382500253835701200000000000000)
      constant := (169706244878189018058066980776025748041718527) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel086
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
  base := (-1337510061624132282619823697222098786481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6421232203660651695065198030480000000000000)
      constant := (105987557459838127403853595009851253802827964) }

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
  base := (-5350111376277536152414971924221674931401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-176274325828294776649929345385680000000000000)
      constant := (2959930467625678255274743478310818270510277997) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel087
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
  base := (-5133291597827383086122545519064243632227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6499943034304838773290713495360000000000000)
      constant := (108710439780061111589451853804150433590286397) }

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
  base := (-25666772987999128910579082161439101989/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-59477750489607016931847827950320000000000000)
      constant := (1011936342159633708410165277110179379145322200) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel088
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
  base := (-2454992277761320987056931397015412732243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6578653864949025851516228960240000000000000)
      constant := (111467627818074742134753204205485091440763546) }

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
  base := (-4910040347183397280395945521207954277837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-180592177109347324941157622316240000000000000)
      constant := (3112641833290595863388726019326494332770037889) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel089
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
  base := (-4680119921673120669886880467038682026067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6657364695593212929741744425120000000000000)
      constant := (114259121342074773540757326030265820894466637) }

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
  base := (-585021165447233157746880628361032664451/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-182751102749873599086771760781520000000000000)
      constant := (3190428882609979826910776333721110896954310776) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel090
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
  base := (-2221849201507890917991501203009098930409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6736075526237400007967259890000000000000000)
      constant := (117084920147814223597989753560660740818223598) }

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
  base := (-1110935535367946160856548264381939211799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-61636676130133291077461966415600000000000000)
      constant := (1089723389880212740594209015345370304440443204) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel091
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
  base := (-4200720622630840192185373462968663906677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6814786356881587086192775354880000000000000)
      constant := (119945024055222910252433157934442056130970347) }

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
  base := (-2100379671066445984661017783715686586647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-187068954030926147378000037712080000000000000)
      constant := (3348865690159058899746977799890052995128786918) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel092
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
  base := (-987796782549015985589218473386254218493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6893497187525774164418290819760000000000000)
      constant := (122839432905443958493171166757725490123422092) }

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
  base := (-987805350635092311202610076556801913191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-189227879671452421523614176177360000000000000)
      constant := (3429515440443373303617659783232589098685482508) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel093
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
  base := (-36950984109764607371277036520276910361/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-6972208018169961242643806284640000000000000)
      constant := (125768146558235781109171652243723997290567100) }

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
  base := (-230945546460826690511433096440784613017/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-63795601770659565223076104880880000000000000)
      constant := (1170373139070341037950754749265880307544684528) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel094
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
  base := (-3432454893705522226457549522737439404341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7050918848814148320869321749520000000000000)
      constant := (128731164889694399013596264911768880012145451) }

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
  base := (-3432481735998309182772998323519855779691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-193545730952504969814842453107920000000000000)
      constant := (3593677617564232848253379931744294565351071127) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel095
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
  base := (-632651391498981530304744066682985378353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7129629679458335399094837214400000000000000)
      constant := (131728487790256542685744762510643086128279915) }

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
  base := (-790820177145852862718541008031206353619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-195704656593031243960456591573200000000000000)
      constant := (3677190038942309196175710518921329987290843772) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel096
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
  base := (-57750098757850740536936663276261763923/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7208340510102522477320352679280000000000000)
      constant := (134760115162948863241420686704298017511312650) }

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
  base := (-1443762975722628936633227874650062575093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-65954527411185839368690243346160000000000000)
      constant := (1253885559693303586695036480804710374484366214) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel097
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
  base := (-651299783048560942155346234378584997537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7287051340746709555545868144160000000000000)
      constant := (137826046921852864823343827881818355742847228) }

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
  base := (-1302608860864152566046756653148945918289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-200022507874083792251684868503760000000000000)
      constant := (3847077535970539344490809880619437549999181866) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel098
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
  base := (-579084951025286753797881368386661214481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7365762171390896633771383609040000000000000)
      constant := (140926282990758924000532726745505019636059964) }

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
  base := (-1158178123749151041971751274194956399833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-202181433514610066397299006969040000000000000)
      constant := (3933452607834597911064854375446593510424206202) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel099
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
  base := (-2020927187803519130951475521720540519273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7444473002035083711996899073920000000000000)
      constant := (144060823301986052059677453498662763789930103) }

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
  base := (-2020941731323998913409349389290654627977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-68113453051712113514304381811440000000000000)
      constant := (1340260631030480834038954775330295007312631823) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel100
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
  base := (-1718961491561945705631671371025681474669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7523183832679270790222414538800000000000000)
      constant := (147229667795346939765345912053773578053820659) }

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
  base := (-1718974353411190144341103517333737694279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-206499284795662614688527283899600000000000000)
      constant := (4109065390334927302977237794534244844771540963) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel101
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
  base := (-56417716033913198945297654984171244569/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7601894663323457868447930003680000000000000)
      constant := (150432816417240351582796407516779362757988975) }

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
  base := (-1410454274345221378211867732205892086843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-208658210436188888834141422364880000000000000)
      constant := (4198303098312004861917680159930717424046364071) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel102
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
  base := (-547685790548814334941368253233547631859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (490)
      previous := (343)
      next := (0)
      square := (5622202188870505587536818920000000000000)
      linear := (-451800323174567349804320321680000000000000)
      constant := (9039427595285597147978498415070059380516794) }

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
  base := (-1095381637491046192365017500948320159991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4361)
      previous := (3136)
      next := (0)
      square := (50599819699834550287831370280000000000000)
      linear := (-4133669334837552215289324722160000000000000)
      constant := (84088137566745067572042765949234907015521377) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel103
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
  base := (-386873840064244207296972743238946431903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7759316324611832024898960933440000000000000)
      constant := (156942025860472184190619017331967888962360066) }

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
  base := (-773756571093760221838679145596118154417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-212976061717241437125369699295440000000000000)
      constant := (4379641142110211574506538005284193490041084149) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel104
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
  base := (-445571330257063777369900784916855238173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7838027155256019103124476398320000000000000)
      constant := (160248086600851936437134532760199028836168003) }

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
  base := (-445579190117153108613132585566717641333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-215134987357767711270983837760720000000000000)
      constant := (4471741476033581796338378861339142902244678601) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel105
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
  base := (-110842650158137665004627010784683820289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7916737985900206181349991863200000000000000)
      constant := (163588451306697395995117546228883226375936479) }

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
  base := (-110849597853108699576657880246957261461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-72431304332764661805532658742000000000000000)
      constant := (1521598672289374180670811460757477664162939939) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel106
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
  base := (230438253504858269804086105916291345281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-7995448816544393259575507328080000000000000)
      constant := (166963119947182831116938396506049808198786209) }

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
  base := (230432112669435243968524171443671643009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-219452838638820259562212114691280000000000000)
      constant := (4658804763887929010177263339190094969830399227) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel107
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
  base := (578271284649289662115076257200360303117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8074159647188580337801022792960000000000000)
      constant := (170372092494540360471129087684690904127600813) }

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
  base := (578265857450858699939211506295228002031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-221611764279346533707826253156560000000000000)
      constant := (4753767716437552165800550506392901664099847893) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel108
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
  base := (932656356518072787947951212587107608853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8152870477832767416026538257840000000000000)
      constant := (173815368923697186861459286410197674098958517) }

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
  base := (116581445055075415377804853001614141047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-74590229973290935951146797207280000000000000)
      constant := (1616561624641189834037939605214217587046905976) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel109
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
  base := (258718678115624258275975323377679793253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8231581308476954494252053722720000000000000)
      constant := (177292949211957248331067293553920747301250585) }

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
  base := (646794576295542143325997626436839732121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-225929615560399081999054530087120000000000000)
      constant := (4946556235807202714715372123507293320859480326) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel110
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
  base := (1661082315553541314080127911870114030237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8310292139121141572477569187600000000000000)
      constant := (180804833338721811554895529718530462954738493) }

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
  base := (1661078571028974625895816668444415311839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-228088541200925356144668668552400000000000000)
      constant := (5044381801597851233297845533623871772678279717) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel111
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
  base := (1017561533288484654140430846293002960487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8389002969765328650703084652480000000000000)
      constant := (184351021285244208467639088159997355711161486) }

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
  base := (127194984895573332761589517653314548323/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-76749155613817210096760935672560000000000000)
      constant := (1714387190282475664876318422810500338243009968) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel112
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
  base := (483143116888899416634041280902213305903/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8467713800409515728928600117360000000000000)
      constant := (187931513034414509602153337999063698227029835) }

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
  base := (75491020683706582851041643442975494683/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-232406392481977904435896945482960000000000000)
      constant := (5242895543145390215603267891264817209120366368) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel113
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
  base := (2802859814961425625064889435003530312259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8546424631053702807154115582240000000000000)
      constant := (191546308570570446943483813450676020260242851) }

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
  base := (1401428616659327663136486403864014727823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-234565318122504178581511083948240000000000000)
      constant := (5343583718114398496336962053175181813842405738) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel114
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
  base := (799138927091916059211612512080594217091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8625135461697889885379631047120000000000000)
      constant := (195195407879331354280163279362205166914957196) }

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
  base := (639310685611259393824496780514098273663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-78908081254343484242375074137840000000000000)
      constant := (1815075365135497525611159543367225848048987315) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel115
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
  base := (899200804708242997213089360755418497849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8703846292342076963605146512000000000000000)
      constant := (198878810947452291983519264332033263783513444) }

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
  base := (1798400602417754694095975253335255973411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-238883169403556726872739360878800000000000000)
      constant := (5547822674699751684719841512427550004721052066) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel116
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
  base := (4003602304013448399850891223790757366707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8782557122986264041830661976880000000000000)
      constant := (202596517762695872814475801165915528878978323) }

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
  base := (2001800262680638865456426374915404099477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-241042095044083001018353499344080000000000000)
      constant := (5651373455695359819101458539605649796376438062) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel117
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
  base := (1104238231165435185222517801234032006003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8861267953630451120056177441760000000000000)
      constant := (206348528313719611834365767590186540998939468) }

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
  base := (4416951353969714794094258735481442033777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-81067006894869758387989212603120000000000000)
      constant := (1918626146038343889377276956682347230729853977) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel118
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
  base := (302303440267772802604217468106757462199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-8939978784274638198281692906640000000000000)
      constant := (210134842589976892117971764832685646505208176) }

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
  base := (483685365733851582956293642206197101673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-245359946325135549309581776274640000000000000)
      constant := (5861337621698753287860962774131429559843544190) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel119
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
  base := (657913578605043870256296070410661062749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (490)
      previous := (343)
      next := (0)
      square := (5622202188870505587536818920000000000000)
      linear := (-530511153818754428029835786560000000000000)
      constant := (12585615328331169024140907580095849904533864) }

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
  base := (5263307404232721824112401293683382438443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (13083)
      previous := (9408)
      next := (0)
      square := (151799459099503650863494110840000000000000)
      linear := (-14559933645038930791482112631760000000000000)
      constant := (351044176835458723124047297245960672539245337) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel120
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
  base := (1424078411619035088590608137518473511453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9097400445563012354732723836400000000000000)
      constant := (217810382279472877233558307278971355379239668) }

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
  base := (1139262513056278291910623749267092352523/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-83225932535396032533603351068400000000000000)
      constant := (2025039530465995076256507256227218536044561615) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel121
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
  base := (6135870067292284016395284557982864877631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9176111276207199432958239301280000000000000)
      constant := (221699607674864962825822176272897047949635359) }

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
  base := (3067934556390666558437133328772159665963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-251836723246714371746424191670480000000000000)
      constant := (6183440377068146090639974475610738323747018578) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel122
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
  base := (6581977863138043716130016569857776510167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9254822106851386511183754766160000000000000)
      constant := (225623136759670566838133571426448897411438263) }

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
  base := (1316395404104906060410253398947895883497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-253995648887240645892038330135760000000000000)
      constant := (6292716363008779726017288391580432157894635455) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel123
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
  base := (703463700743047620605315026933953382651/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9333532937495573589409270231040000000000000)
      constant := (229580969526207218671961097506199125275861390) }

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
  base := (7034636263646315418111682569598112235121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-85384858175922306679217489533680000000000000)
      constant := (2134315516341955711214095863070084689923549721) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel124
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
  base := (468365467187187687934425896997867198311/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9412243768139760667634785695920000000000000)
      constant := (233573105967199465146811945705158137924990064) }

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
  base := (1498769363698343095511950673607727665367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-258313500168293194183266607066320000000000000)
      constant := (6514130934934828559293542653110325494864293505) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel125
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
  base := (1989902310481209390850964980828456365223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9490954598783947745860301160800000000000000)
      constant := (237599546075738244948169981992837695558197788) }

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
  base := (7959608662497715777533102443557054944441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-260472425808819468328880745531600000000000000)
      constant := (6626269520559604799244618455967075699731473123) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel126
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
  base := (263497571420530168272542252129354919171/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9569665429428134824085816625680000000000000)
      constant := (241660289845245046888225526178732274292493408) }

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
  base := (8431921774089469550408939998915552448341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-87543783816448580824831627998960000000000000)
      constant := (2246454101910615774722584789664219351918134941) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel127
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
  base := (8910786583862656620302403563799061204633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9648376260072321902311332090560000000000000)
      constant := (245755337269440268040154921855497928688138937) }

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
  base := (8910786132588728229890500926148374443433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-264790277089872016620109022462160000000000000)
      constant := (6853409290290203760500136734049615765782107699) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel128
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
  base := (9396202116350739315755296222304522672909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9727087090716508980536847555440000000000000)
      constant := (249884688342315259709138962466806007052470701) }

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
  base := (1879240343626596534950288984293575211607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-266949202730398290765723160927440000000000000)
      constant := (6968410474079686949412776417747493836880847105) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel129
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
  base := (2472042215745519920932514369776982687563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9805797921360696058762363020320000000000000)
      constant := (254048343058107612230633505941502191986822828) }

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
  base := (9888168511603994350231071457160041879463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-89702709456974854970445766464240000000000000)
      constant := (2361455285650372425206311891289513268928483263) }

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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556807508997610921653/100000000000000000000)
  centralHi := (278403754498805460827/50000000000000000000)
  directionLo := (558978306739039999623/100000000000000000000)
  directionHi := (69872288342379999953/12500000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree130.table
  base := (10386686804593906894748249758794300189847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9884508752004883136987878485200000000000000)
      constant := (258246301411279284834919283820291552754865783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree130.table
  base := (649167905910285029640615715425474476999/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-271267054011450839056951437858000000000000000)
      constant := (7201275438760629245810047936951439637504371152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558978306739039999623/100000000000000000000)
  centralHi := (69872288342379999953/12500000000000000000)
  directionLo := (280570353357925190927/50000000000000000000)
  directionHi := (112228141343170076371/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree131.table
  base := (5445877961366393736543563070810065925099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-9963219582649070215213393950080000000000000)
      constant := (262478563396497235247512422243368218104707222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree131.table
  base := (2178351129840500291979546956946792815487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-273425979651977113202565576323280000000000000)
      constant := (7319139219369234422669454086021599121696225305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280570353357925190927/50000000000000000000)
  centralHi := (112228141343170076371/20000000000000000000)
  directionLo := (563294805641134717737/100000000000000000000)
  directionHi := (281647402820567358869/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree132.table
  base := (5701688099797600642463156678392919015787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10041930413293257293438909414960000000000000)
      constant := (266745129008616246149738833335471107191124886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree132.table
  base := (5701687979140492611122436145144825210927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-91861635097501129116059904929520000000000000)
      constant := (2479319066214144601812815502640803380747242254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563294805641134717737/100000000000000000000)
  centralHi := (281647402820567358869/50000000000000000000)
  directionLo := (282720349192892135993/50000000000000000000)
  directionHi := (565440698385784271987/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree133.table
  base := (11921547617974799884432245111626422067121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10120641243937444371664424879840000000000000)
      constant := (271045998242663682840752616438020035977397969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree133.table
  base := (11921547405094413335929572042711545707297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-277743830933029661493793853253840000000000000)
      constant := (7557729376449873609603927920596158191154038491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282720349192892135993/50000000000000000000)
  centralHi := (565440698385784271987/100000000000000000000)
  directionLo := (567578478027244425739/100000000000000000000)
  directionHi := (28378923901362221287/5000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree134.table
  base := (12446270161215540876616637247147252839673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10199352074581631449889940344720000000000000)
      constant := (275381171093825949068402157429065556070665497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree134.table
  base := (6223134986714595307404291438109889989713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-279902756573555935639407991719120000000000000)
      constant := (7678455752665039151928422535196262943179461078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567578478027244425739/100000000000000000000)
  centralHi := (28378923901362221287/5000000000000000000)
  directionLo := (569708235896623585553/100000000000000000000)
  directionHi := (284854117948311792777/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree135.table
  base := (6488771906584995462746095911032017078479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10278062905225818528115455809600000000000000)
      constant := (279750647557436436598587127203576505871360862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree135.table
  base := (6488771823764392085866718183644149654821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-94020560738027403261674043394800000000000000)
      constant := (2600045442388327402097836950871316866504378842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569708235896623585553/100000000000000000000)
  centralHi := (284854117948311792777/50000000000000000000)
  directionLo := (114366012324844592311/20000000000000000000)
  directionHi := (142957515406055740389/25000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree136.table
  base := (13515368558162176801725252903173160758129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (490)
      previous := (343)
      next := (0)
      square := (5622202188870505587536818920000000000000)
      linear := (-609221984462941506255351251440000000000000)
      constant := (16714966331115575833413535246873943732888193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree136.table
  base := (13515368412062551922948733636460088424309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (13083)
      previous := (9408)
      next := (0)
      square := (151799459099503650863494110840000000000000)
      linear := (-16718859285565204937096251097040000000000000)
      constant := (466045358813533986618802911493695180586757831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114366012324844592311/20000000000000000000)
  centralHi := (142957515406055740389/25000000000000000000)
  directionLo := (114788808636710286739/20000000000000000000)
  directionHi := (17935751349485982303/3125000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree137.table
  base := (1405974438095443993266437992262589190381/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10435484566514192684566486739360000000000000)
      constant := (288592511304007323449234807084798882760201090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree137.table
  base := (3514936063024471288723248801624974740923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-286379533495134758076250407114960000000000000)
      constant := (8046360070543806704814918239171998711613688676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114788808636710286739/20000000000000000000)
  centralHi := (17935751349485982303/3125000000000000000)
  directionLo := (4500392710420989541/781250000000000000)
  directionHi := (576050266933886661249/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree138.table
  base := (14610671266717816610158518339684128607409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10514195397158379762792002204240000000000000)
      constant := (293064898578278468930545596105128713167541201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree138.table
  base := (14610671153075266331966371829822733026437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-96179486378553677407288181860080000000000000)
      constant := (2723634413064187029283010486757528928601762637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4500392710420989541/781250000000000000)
  centralHi := (576050266933886661249/100000000000000000000)
  directionLo := (578148817661440694317/100000000000000000000)
  directionHi := (289074408830720347159/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree139.table
  base := (7584074600502762242810924010527750425103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10592906227802566841017517669120000000000000)
      constant := (297571589447603105513221164239325039745709534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree139.table
  base := (3033629820157178561414265424887803281569/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-290697384776187306367478684045520000000000000)
      constant := (8296400605665469634566687082305917645030414535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578148817661440694317/100000000000000000000)
  centralHi := (289074408830720347159/50000000000000000000)
  directionLo := (14505994465479640171/2500000000000000000)
  directionHi := (580239778619185606841/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree140.table
  base := (15732178169729187252009769263501448077439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10671617058446753919243033134000000000000000)
      constant := (302112583907909692444525622173151918494379871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree140.table
  base := (3146435616270312078005705471733656292017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-292856310416713580513092822510800000000000000)
      constant := (8422852169854240717671915764163688600233043255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14505994465479640171/2500000000000000000)
  centralHi := (580239778619185606841/100000000000000000000)
  directionLo := (291161615782696039459/50000000000000000000)
  directionHi := (582323231565392078919/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree141.table
  base := (3260551631827494873609556483479437921457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10750327889090940997468548598880000000000000)
      constant := (306687881955224095198030639507867787796505365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree141.table
  base := (8151379040603269304260477033906318285849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-98338412019079951552902320325360000000000000)
      constant := (2850085977217673647429742603588620667722986498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291161615782696039459/50000000000000000000)
  centralHi := (582323231565392078919/100000000000000000000)
  directionLo := (11687985136018628063/2000000000000000000)
  directionHi := (584399256800931403151/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree142.table
  base := (16879889155796872100637639010115792493267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10829038719735128075694064063760000000000000)
      constant := (311297483585664028304870822434883464030554163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree142.table
  base := (3375977817416240528160592710427648926117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-297174161697766128804321099441360000000000000)
      constant := (8678617890958267425934541964323414722852454755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11687985136018628063/2000000000000000000)
  centralHi := (584399256800931403151/100000000000000000000)
  directionLo := (117293586641077813371/20000000000000000000)
  directionHi := (73308491650673633357/12500000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree143.table
  base := (17463571146574336730037523903310707208461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10907749550379315153919579528640000000000000)
      constant := (315941388795434042130040786379216794383245229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree143.table
  base := (698542843439488636106273168297464969117/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-299333087338292402949935237906640000000000000)
      constant := (8807932047668632178241207304143707978850498775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117293586641077813371/20000000000000000000)
  centralHi := (73308491650673633357/12500000000000000000)
  directionLo := (29426466913601793083/5000000000000000000)
  directionHi := (588529338272035861661/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree144.table
  base := (18053804118621611077927908691625737678453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-10986460381023502232145094993520000000000000)
      constant := (320619597580820990349006187631719838189072917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree144.table
  base := (18053804065204082652082352302972836361147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-100497337659606225698516458790640000000000000)
      constant := (2979400133894952390311465426510272347375343347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29426466913601793083/5000000000000000000)
  centralHi := (588529338272035861661/100000000000000000000)
  directionLo := (73822943517712548351/12500000000000000000)
  directionHi := (590583548141700386809/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree145.table
  base := (18650588059361012105674765709184605204967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-11065171211667689310370610458400000000000000)
      constant := (325332109938189922563601792196954350904235463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree145.table
  base := (9325294006133456093985841735550885051863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-303650938619344951241163514837200000000000000)
      constant := (9069422952909678861873364341869007112119373978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73822943517712548351/12500000000000000000)
  centralHi := (590583548141700386809/100000000000000000000)
  directionLo := (9259853713056013059/1562500000000000000)
  directionHi := (592630637635584835777/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree146.table
  base := (19253922956472520648959476021588280592551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-11143882042311876388596125923280000000000000)
      constant := (330078925863980353235339519202879013091247239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree146.table
  base := (962696145747762783027348477946878862259/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-305809864259871225386777653302480000000000000)
      constant := (9201599701247741088683294903006309915244139540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9259853713056013059/1562500000000000000)
  centralHi := (592630637635584835777/100000000000000000000)
  directionLo := (297335340143532040579/50000000000000000000)
  directionHi := (594670680287064081159/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree147.table
  base := (620744024933813275270717225713211678891/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-11222592872956063466821641388160000000000000)
      constant := (334860045354702864025373952100155781606383968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree147.table
  base := (4965952190320723382212271891503135884083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-102656263300132499844130597255920000000000000)
      constant := (3111576882201838460095361308723358625737999532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297335340143532040579/50000000000000000000)
  centralHi := (594670680287064081159/100000000000000000000)
  directionLo := (596703748372506294211/100000000000000000000)
  directionHi := (149175937093126573553/25000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree148.table
  base := (20480245571750586459837375809847592909843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-11301303703600250545047156853040000000000000)
      constant := (339675468406936001815595172208405954350944627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree148.table
  base := (10240122769744233298842690573485668171831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-310127715540923773678005930233040000000000000)
      constant := (9468815788891227850881643113897497337489594586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (596703748372506294211/100000000000000000000)
  centralHi := (149175937093126573553/25000000000000000000)
  directionLo := (598729912941151647569/100000000000000000000)
  directionHi := (59872991294115164757/10000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree149.table
  base := (21103233266464616080544360873958968152203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-11380014534244437623272672317920000000000000)
      constant := (344525195017323439234162985133014141795986667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree149.table
  base := (10551616619013428304375157286336014561281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-312286641181450047823620068698320000000000000)
      constant := (9603855128014791942700414370894079843243351286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598729912941151647569/100000000000000000000)
  centralHi := (59872991294115164757/10000000000000000000)
  directionLo := (600749243844084047071/100000000000000000000)
  directionHi := (18773413870127626471/3125000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree150.table
  base := (21732771870626854911755653954503090038037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-11458725364888624701498187782800000000000000)
      constant := (349409225182571368499718225912851393020992693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree150.table
  base := (21732771845561233780341518825649669694787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-104815188940658773989744735721200000000000000)
      constant := (3246616221295915457651924703905514790876140987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (600749243844084047071/100000000000000000000)
  centralHi := (18773413870127626471/3125000000000000000)
  directionLo := (30138090488116465833/5000000000000000000)
  directionHi := (602761809762329316661/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree151.table
  base := (174756729476938090440570013514353796251/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-11537436195532811779723703247680000000000000)
      constant := (354327558899446102900285267777962975630916992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree151.table
  base := (2236886135095569869033323507464102818849/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-316604492462502596114848345628880000000000000)
      constant := (9876796396423197718456875040204543942954787470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30138090488116465833/5000000000000000000)
  centralHi := (602761809762329316661/100000000000000000000)
  directionLo := (302383839117055907143/50000000000000000000)
  directionHi := (604767678234111814287/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree152.table
  base := (23011501762739422918508366763592093185691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-11616147026176998857949218712560000000000000)
      constant := (359280196164771863295795162589238114930664699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree152.table
  base := (23011501743268454655466473249491531249707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-318763418103028870260462484094160000000000000)
      constant := (10014698325535767139684247256840662418341463721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302383839117055907143/50000000000000000000)
  centralHi := (604767678234111814287/100000000000000000000)
  directionLo := (60676691568130008243/10000000000000000000)
  directionHi := (606766915681300082431/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree153.table
  base := (4732138605781065231083261238056785039117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (490)
      previous := (343)
      next := (0)
      square := (5622202188870505587536818920000000000000)
      linear := (-687932815107128584480866716320000000000000)
      constant := (21427478645613454690003046039914826728324945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree153.table
  base := (4732138602349090886386198310187824915981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4361)
      previous := (3136)
      next := (0)
      square := (50599819699834550287831370280000000000000)
      linear := (-6292594975363826360903463187440000000000000)
      constant := (199089302963559623646949793036573686060725465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60676691568130008243/10000000000000000000)
  centralHi := (606766915681300082431/100000000000000000000)
  directionLo := (608759587435070830243/100000000000000000000)
  directionHi := (152189896858767707561/25000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree154.table
  base := (3039554395117115203318306631471687289787/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-11773568687465373014400249642320000000000000)
      constant := (369288381328350740605150303555002541013987544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree154.table
  base := (12158217572907235891761579329733949570277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-323081269384081418551690761024720000000000000)
      constant := (10293364773158023636066354669092148016993742862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608759587435070830243/100000000000000000000)
  centralHi := (152189896858767707561/25000000000000000000)
  directionLo := (305372878880409650829/50000000000000000000)
  directionHi := (610745757760819301659/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree155.table
  base := (24978728148405932613386503153360334050969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-11852279518109560092625765107200000000000000)
      constant := (374343929220524123949440669306321136540730041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree155.table
  base := (4995745627015910870642991005175195675149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-325240195024607692697304899490000000000000000)
      constant := (10434129291504096013658103292978910259265938235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305372878880409650829/50000000000000000000)
  centralHi := (610745757760819301659/100000000000000000000)
  directionLo := (612725489882342901559/100000000000000000000)
  directionHi := (15318137247058572539/2500000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree156.table
  base := (6411892995264739754562665294096637928331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-11930990348753747170851280572080000000000000)
      constant := (379433780648985647134691685085415713445150636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree156.table
  base := (25647571969315819435685808630975666467313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-109133040221711322280973012651760000000000000)
      constant := (3525282668699991059673356297686607708481481113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612725489882342901559/100000000000000000000)
  centralHi := (15318137247058572539/2500000000000000000)
  directionLo := (122939769201064765397/20000000000000000000)
  directionHi := (307349423002661913493/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree157.table
  base := (26322966648812135233711158815655358469627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12009701179397934249076796036960000000000000)
      constant := (384557935610821073000356725852084398597722203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree157.table
  base := (26322966638464558773183705463233430912077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-329558046305660240988533176420560000000000000)
      constant := (10718520916867167031617012504002890461406936831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122939769201064765397/20000000000000000000)
  centralHi := (307349423002661913493/50000000000000000000)
  directionLo := (308332943670067689619/50000000000000000000)
  directionHi := (616665887340135379239/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree158.table
  base := (540098242834922388079627847983817219267/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12088412010042121327302311501840000000000000)
      constant := (389716394103163711750113463145126158818408150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree158.table
  base := (1350245606631431123225074243732070236401/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-331716971946186515134147314885840000000000000)
      constant := (10862148023728450110769814651271706881092740060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308332943670067689619/50000000000000000000)
  centralHi := (616665887340135379239/100000000000000000000)
  directionLo := (154656668530998903177/25000000000000000000)
  directionHi := (618626674123995612709/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree159.table
  base := (553868169002027631145747313039123718227/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12167122840686308405527826966720000000000000)
      constant := (394909156123193059222119212041055337728380150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree159.table
  base := (86541901381462673613835828496417068217/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-111291965862237596426587151117040000000000000)
      constant := (3668909775535940515992854860733177854218373440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154656668530998903177/25000000000000000000)
  centralHi := (618626674123995612709/100000000000000000000)
  directionLo := (620581265642491004579/100000000000000000000)
  directionHi := (31029063282124550229/5000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree160.table
  base := (14194227782136880923522734546287416710019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12245833671330495483753342431600000000000000)
      constant := (400136221668133513220711309399754126858390982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree160.table
  base := (28388455557195963939613592214905687184277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-336034823227239063425375591816400000000000000)
      constant := (11152264825430474808508019431572909077098913431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620581265642491004579/100000000000000000000)
  centralHi := (31029063282124550229/5000000000000000000)
  directionLo := (622529720250491903647/100000000000000000000)
  directionHi := (19454053757827871989/3125000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree161.table
  base := (29090053474810273443208426263327671512133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12324544501974682561978857896480000000000000)
      constant := (405397590735253160552006092324941697067006437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree161.table
  base := (14545026734287294424798622596645700437933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-338193748867765337570989730281680000000000000)
      constant := (11298754520122767060719077367966772801034382398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622529720250491903647/100000000000000000000)
  centralHi := (19454053757827871989/3125000000000000000)
  directionLo := (624472095392480633879/100000000000000000000)
  directionHi := (15611802384812015847/2500000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree162.table
  base := (1489910108620256375967147015852801529137/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12403255332618869640204373361360000000000000)
      constant := (410693263321862628245164338027789192838411860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree162.table
  base := (29798202166911571625275634063150831026921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-113450891502763870572201289582320000000000000)
      constant := (3815399470204063343326384440360815311501021521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624472095392480633879/100000000000000000000)
  centralHi := (15611802384812015847/2500000000000000000)
  directionLo := (31320422381115614343/5000000000000000000)
  directionHi := (626408447622312286861/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree163.table
  base := (244103213183167682678979746985552709611/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12481966163263056718429888826240000000000000)
      constant := (416023239425313993179159425615813091634697375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree163.table
  base := (15256450821528196221101053473926006197317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-342511600148817885862218007212240000000000000)
      constant := (11594596496827342210098090066326569252715329102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31320422381115614343/5000000000000000000)
  centralHi := (626408447622312286861/100000000000000000000)
  directionLo := (314169416311213717293/50000000000000000000)
  directionHi := (628338832622427434587/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree164.table
  base := (15617075946130122329190801926809666399021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12560676993907243796655404291120000000000000)
      constant := (421387519042999744984112302587935987178634138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree164.table
  base := (195213449299981053451538801609330426809/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-344670525789344160007832145677520000000000000)
      constant := (11743948778697902319392225658731136851262500320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314169416311213717293/50000000000000000000)
  centralHi := (628338832622427434587/100000000000000000000)
  directionLo := (630263305222535228373/100000000000000000000)
  directionHi := (315131652611267614187/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree165.table
  base := (1278478115864474790185601896362413001609/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12639387824551430874880919756000000000000000)
      constant := (426786102172351797657541412432218433936625025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree165.table
  base := (15980976446428199577822340848196389520151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-115609817143290144717815428047600000000000000)
      constant := (3964751752051534633640335803140317618283825502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630263305222535228373/100000000000000000000)
  centralHi := (315131652611267614187/50000000000000000000)
  directionLo := (632181919417784618801/100000000000000000000)
  directionHi := (316090959708892309401/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree166.table
  base := (16348152326098937949019956804783793391267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12718098655195617953106435220880000000000000)
      constant := (432218988810840545838746076259405032580152326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree166.table
  base := (6539260929777969086698259792513120388083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-348988377070396708299060422608080000000000000)
      constant := (12045515929129210977380510018955619391941058245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632181919417784618801/100000000000000000000)
  centralHi := (316090959708892309401/50000000000000000000)
  directionLo := (634094728386440734051/100000000000000000000)
  directionHi := (158523682096610183513/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree167.table
  base := (6687441430079066181490095370743179730589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12796809485839805031331950685760000000000000)
      constant := (437686178955973962127379514370683894710701105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree167.table
  base := (4179650893435191937771726047758659452417/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-351147302710922982444674561073360000000000000)
      constant := (12197730797554494680762907087523366557657678808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (634094728386440734051/100000000000000000000)
  centralHi := (158523682096610183513/25000000000000000000)
  directionLo := (159000446126770696953/25000000000000000000)
  directionHi := (636001784507082787813/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree168.table
  base := (34184660382708337547429491189751475838343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12875520316483992109557466150640000000000000)
      constant := (443187672605296732222398917685998176517281127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree168.table
  base := (34184660380141885137003454247089377314233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74137)
      previous := (53312)
      next := (0)
      square := (860196934897187354893133294760000000000000)
      linear := (-117768742783816418863429566512880000000000000)
      constant := (4116966620454736928454317418112039470394320033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell021.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159000446126770696953/25000000000000000000)
  centralHi := (636001784507082787813/100000000000000000000)
  directionLo := (159475784843834812919/25000000000000000000)
  directionHi := (637903139375339251677/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree169.table
  base := (34938664340765161830579130825442469578123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (8330)
      previous := (5831)
      next := (0)
      square := (95577437210798594988125921640000000000000)
      linear := (-12954231147128179187782981615520000000000000)
      constant := (448723469756389425001446314551392873708077547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree169.table
  base := (8734666084626181517147317476687236512543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (222411)
      previous := (159936)
      next := (0)
      square := (2580590804691562064679399884280000000000000)
      linear := (-355465153991975530735902838003920000000000000)
      constant := (12505023120493078080174587806617082026029492116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell021.Kernel169
