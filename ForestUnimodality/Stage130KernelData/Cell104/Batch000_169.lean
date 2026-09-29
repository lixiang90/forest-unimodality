import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell104.Parameters
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch000_049
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch050_099
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch100_149
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch150_199
import ForestUnimodality.BinomialMassData.Q27_52.Batch000_049
import ForestUnimodality.BinomialMassData.Q27_52.Batch050_099
import ForestUnimodality.BinomialMassData.Q27_52.Batch100_149
import ForestUnimodality.BinomialMassData.Q27_52.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree000.table
  base := (179882100390517146817330741/2000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (62018319898615621721393865000000000000)
      linear := (-3058515157179239607465604000000000000)
      constant := (89941050195258573408665370500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree000.table
  base := (179882100390517146817330741/2000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (62018319898615621721393865000000000000)
      linear := (-3058515157179239607465604000000000000)
      constant := (89941050195258573408665370500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree001.table
  base := (504713088061270050521045017303315361794549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-1626681262394858608350224290297023750000000000)
      constant := (1218731063700037371277312709491004067744138329023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree001.table
  base := (504272303890352574822930875317587472534051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-114011042037703331057663103835000000000000)
      constant := (85252960301523816670477679075922907858254619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9992600812897369001/20000000000000000000)
  directionHi := (24981502032243422503/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree002.table
  base := (297375064042965270935279955612249728977201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-3179535260126632292660749815528967500000000000)
      constant := (719499315610263572535259898426548423266600158227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree002.table
  base := (296913190243117266540529574132454350154981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-222853193459773747178709336910000000000000)
      constant := (50296725233202894581447840482367285176191789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9992600812897369001/20000000000000000000)
  centralHi := (24981502032243422503/50000000000000000000)
  directionLo := (70658357964899368217/100000000000000000000)
  directionHi := (35329178982449684109/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree003.table
  base := (18621800798505044236282419243162790119023/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 268203000000000000000000000000000000000000000
      center := (4827654)
      previous := (2413827)
      next := (2413827)
      square := (16633499451768405592542998774595000000000000)
      linear := (-52582102865093399744125281564010125000000000)
      constant := (5035968586636740794340844038344131091261075669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree003.table
  base := (92924083833302407287239133730013230180029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-165847672440922081649877784992500000000000)
      constant := (15835352874920874347587385560470048400424901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70658357964899368217/100000000000000000000)
  centralHi := (35329178982449684109/50000000000000000000)
  directionLo := (86538461538461538461/100000000000000000000)
  directionHi := (43269230769230769231/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree004.table
  base := (124770858732659860754495713883561799088581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-6285243255590179661281800865992855000000000000)
      constant := (307771533126900650335636031551453243683592209487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree004.table
  base := (15562517941060800437111160856910093749001/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-220268748151957289710400901530000000000000)
      constant := (10751686598288404602172727512216223374324676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86538461538461538461/100000000000000000000)
  centralHi := (43269230769230769231/50000000000000000000)
  directionLo := (99926008128973690011/100000000000000000000)
  directionHi := (24981502032243422503/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree005.table
  base := (89298240008274882509649125514851012046887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-7838097253321953345592326391224798750000000000)
      constant := (225809304485211514143525032171207372098288606549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree005.table
  base := (89104970297399393750868018975839870300271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-549379647725984995541848036135000000000000)
      constant := (15778586640607790023844702537982563080745799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/100000000000000000000)
  centralHi := (24981502032243422503/25000000000000000000)
  directionLo := (111720673448290871687/100000000000000000000)
  directionHi := (13965084181036358961/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree006.table
  base := (16906925383039571059056985463369503371961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-173906504649143093146349109564013750000000000)
      constant := (3295709217238000003436396947273528395038370722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree006.table
  base := (67488219605687628874158017341142540031009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-658221799148055411662894269210000000000000)
      constant := (12438867687800800711551174206375589265240521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111720673448290871687/100000000000000000000)
  centralHi := (13965084181036358961/12500000000000000000)
  directionLo := (61191932987297381919/50000000000000000000)
  directionHi := (122383865974594763839/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree007.table
  base := (26741683776414826227496250276277909801303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-5471902624392750357106688720844343125000000000)
      constant := (74549817263126698217202302026171779959293566581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree007.table
  base := (13344838261486868355012986163835414310641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-383531975285062913891970251142500000000000)
      constant := (5212247673652313438485665013306682536996658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61191932987297381919/50000000000000000000)
  centralHi := (122383865974594763839/100000000000000000000)
  directionLo := (132189683508341538651/100000000000000000000)
  directionHi := (33047420877085384663/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree008.table
  base := (8719637108370186584572513149854321441969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-2499331849303454879704780593384126000000000000)
      constant := (26263443053570731946126180475580112663303705363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree008.table
  base := (43517195257178091902743170389637508300457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-875906101992196243904986735360000000000000)
      constant := (9184330983110127323003849439328738902777233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132189683508341538651/100000000000000000000)
  centralHi := (33047420877085384663/25000000000000000000)
  directionLo := (70658357964899368217/50000000000000000000)
  directionHi := (28263343185959747287/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree009.table
  base := (36245930230196602816073909878741359779239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (16092180)
      previous := (8046090)
      next := (8046090)
      square := (55444998172561351975143329248650000000000000)
      linear := (-520352342379594373438312166376021250000000000)
      constant := (4461267807155434051597259111080750094686245839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree009.table
  base := (36180074294883232805356565995805211294547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-984748253414266660026032968435000000000000)
      constant := (8427412036597435543296835719871705708778443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70658357964899368217/50000000000000000000)
  centralHi := (28263343185959747287/20000000000000000000)
  directionLo := (18736126524182566877/12500000000000000000)
  directionHi := (149889012193460535017/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree010.table
  base := (6098719912238684992186798441804520831211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-3120473448396164353428990803476903500000000000)
      constant := (22851715109365837070925428079764024698189554497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree010.table
  base := (1521903428678380317458985036028419486233/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-109359040483633707614707920151000000000000)
      constant := (799658175981784756524788807093855786346754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18736126524182566877/12500000000000000000)
  centralHi := (149889012193460535017/100000000000000000000)
  directionLo := (78998445794014343287/50000000000000000000)
  directionHi := (6319875663521147463/4000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree011.table
  base := (25819956278265970761051214717466495350323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-17155221239712595451455479542616461250000000000)
      constant := (111472072965423360532592193696603782564171616121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree011.table
  base := (25771875150851278614249699494489826648631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-1202432556258407492268125434585000000000000)
      constant := (7804077955509154556383280605794405703618639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78998445794014343287/50000000000000000000)
  centralHi := (6319875663521147463/4000000000000000000)
  directionLo := (2071356723511308411/1250000000000000000)
  directionHi := (165708537880904672881/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree012.table
  base := (21920347142712348872802915235263484830661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (48276540)
      previous := (24138270)
      next := (24138270)
      square := (166334994517684055925429987745950000000000000)
      linear := (-2078675026382707681751778340872045000000000000)
      constant := (12373260315084797183413166237508909297037772183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree012.table
  base := (4375599445382164446634194536512488822241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-262254941536095581677834333532000000000000)
      constant := (1559721932900239458322631735224610610958729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2071356723511308411/1250000000000000000)
  centralHi := (165708537880904672881/100000000000000000000)
  directionLo := (173076923076923076923/100000000000000000000)
  directionHi := (43269230769230769231/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree013.table
  base := (18606378744542603552990702839180189543561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2570940)
      previous := (1285470)
      next := (1285470)
      square := (8858076631119269250466685737950000000000000)
      linear := (-119887155237728655740097814160238750000000000)
      constant := (671394296202324276966087013933098576938181763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree013.table
  base := (9284354117325285238994977730883701159737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (90)
      previous := (45)
      next := (45)
      square := (310091599493078108606969325000000000000)
      linear := (-4201529168942450664231413907500000000000)
      constant := (23516127505783455899151981736196201159737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173076923076923076923/100000000000000000000)
  centralHi := (43269230769230769231/25000000000000000000)
  directionLo := (11259010814420189073/6250000000000000000)
  directionHi := (180144173030723025169/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree014.table
  base := (15753969892862167721863734451655506156983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-21813783232907916504387056118312292500000000000)
      constant := (117491442103938784831829083054564124679141803941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree014.table
  base := (628812034397264708627473911500268918383/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-305791802104923748126252826762000000000000)
      constant := (1646539143356102382260713570078227236033635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11259010814420189073/6250000000000000000)
  centralHi := (180144173030723025169/100000000000000000000)
  directionLo := (46736110805825915127/25000000000000000000)
  directionHi := (186944443223303660509/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree015.table
  base := (2655227409862645035294277654828057968793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 178802000000000000000000000000000000000000000
      center := (3218436)
      previous := (1609218)
      next := (1609218)
      square := (11088999634512270395028665849730000000000000)
      linear := (-173086201708442149545908012174401750000000000)
      constant := (912791094515240654167999545726408093280562993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree015.table
  base := (2649199381482322154242969821946139115803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-327560232389337831350462073377000000000000)
      constant := (1727335601793090211440168690767022510570707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46736110805825915127/25000000000000000000)
  centralHi := (186944443223303660509/100000000000000000000)
  directionLo := (9675294133412551571/5000000000000000000)
  directionHi := (193505882668251031421/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree016.table
  base := (2221695133016041926388822079086802221697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-4983898245674292774601621433755236000000000000)
      constant := (26103248317239016266222690300277024546392204419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree016.table
  base := (5540751789419081410092781083964123035443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-873321656684379786436678299980000000000000)
      constant := (4574766245302486079141778750069936792989867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9675294133412551571/5000000000000000000)
  centralHi := (193505882668251031421/100000000000000000000)
  directionLo := (99926008128973690011/50000000000000000000)
  directionHi := (199852016257947380023/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree017.table
  base := (9201200923596132283004891807890741129001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-26472345226103237557318632694008123750000000000)
      constant := (139239601649432119000254234717625265666880596827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree017.table
  base := (1147137208774744212085307510604246942619/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-927742732395414994497201416517500000000000)
      constant := (4881427970110412053255908473523783433210444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/50000000000000000000)
  centralHi := (199852016257947380023/100000000000000000000)
  directionLo := (103001371565521874971/50000000000000000000)
  directionHi := (206002743131043749943/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree018.table
  base := (300584507426381140296659713822980501851/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 178802000000000000000000000000000000000000000
      center := (3218436)
      previous := (1609218)
      next := (1609218)
      square := (11088999634512270395028665849730000000000000)
      linear := (-207594068324703786975030801624000500000000000)
      constant := (1105933693936002574632601768967987430479906255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree018.table
  base := (1873278720629519845152419241235317082769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-982163808106450202557724533055000000000000)
      constant := (5234972545643293061244710229108787173975922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103001371565521874971/50000000000000000000)
  centralHi := (206002743131043749943/100000000000000000000)
  directionLo := (211975073894698104651/100000000000000000000)
  directionHi := (52993768473674526163/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree019.table
  base := (6016377154532036200253616689910590073759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-29578053221566784925939683744472011250000000000)
      constant := (160622534490400196671908949336854437523158965693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree019.table
  base := (749655585887053349257374257298500424433/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-1036584883817485410618247649592500000000000)
      constant := (5632669732225800548024939532461598786916708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211975073894698104651/100000000000000000000)
  centralHi := (52993768473674526163/25000000000000000000)
  directionLo := (10889184281640504371/5000000000000000000)
  directionHi := (217783685632810087421/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree020.table
  base := (935959270116537872074358115477723904449/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-6226181443859711722050041853940791000000000000)
      constant := (34627922954494598104026561407765552234104416323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree020.table
  base := (4662806663779889901593135877058539889387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-2182011919057041237357541532260000000000000)
      constant := (12144530068709994107204293209672893241306403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10889184281640504371/5000000000000000000)
  centralHi := (217783685632810087421/100000000000000000000)
  directionLo := (1787530775172653947/800000000000000000)
  directionHi := (13965084181036358961/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree021.table
  base := (3482634032968814225033138607542799628421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (48276540)
      previous := (24138270)
      next := (24138270)
      square := (166334994517684055925429987745950000000000000)
      linear := (-3631529024114481366062303866103988750000000000)
      constant := (20755401676561575604376059238378290043428897463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree021.table
  base := (3467579794267256698738637953687898093389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-2290854070479111653478587765335000000000000)
      constant := (13103761551968860327196647397498879777782741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1787530775172653947/800000000000000000)
  centralHi := (13965084181036358961/6250000000000000000)
  directionLo := (228959248072897262639/100000000000000000000)
  directionHi := (2861990600911215783/1250000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree022.table
  base := (240627033136843140365702959208671820049/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2413827000000000000000000000000000000000000000
      center := (43448886)
      previous := (21724443)
      next := (21724443)
      square := (149701495065915650332886988971355000000000000)
      linear := (-3423661521476210597887126032016784250000000000)
      constant := (20155459029442407388323705441725715970248417523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree022.table
  base := (1196479301750669928753412472020948121839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-1199848110950591034799816999205000000000000)
      constant := (7069944794471767548798427747612790232590791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228959248072897262639/100000000000000000000)
  centralHi := (2861990600911215783/1250000000000000000)
  directionLo := (58586815418047791061/25000000000000000000)
  directionHi := (46869452334438232849/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree023.table
  base := (89691385918554771110923890029101919397/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (410670)
      previous := (205335)
      next := (205335)
      square := (1414947968486915409573601029975000000000000)
      linear := (-33827475626175689662742708738563125000000000)
      constant := (205453478942566718577046870794753801309418088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree023.table
  base := (1423314147130651465057886570036407949601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-2508538373323252485720680231485000000000000)
      constant := (15250272888038616961134989565856777943482569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58586815418047791061/25000000000000000000)
  centralHi := (46869452334438232849/20000000000000000000)
  directionLo := (14975884368241721489/6250000000000000000)
  directionHi := (9584565995674701753/4000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree024.table
  base := (69480125448429204929205371246642848211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-691524503893067654583190951307995000000000000)
      constant := (4337266661950708204601190860627745719091646444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree024.table
  base := (545491827962472043211659357287984436363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-2617380524745322901841726464560000000000000)
      constant := (16432688322328536325998601982221669369745347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14975884368241721489/6250000000000000000)
  centralHi := (9584565995674701753/4000000000000000000)
  directionLo := (244767731949189527677/100000000000000000000)
  directionHi := (122383865974594763839/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree025.table
  base := (-121246075833279057169802231899265119083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-19447588603978713515901418447931836875000000000)
      constant := (126027828186990958421226018144406645602742989359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree025.table
  base := (-125796807484536053092969163886201273913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-1363111338083696658981386348817500000000000)
      constant := (8842631241355030268599826474123544484708703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244767731949189527677/100000000000000000000)
  centralHi := (122383865974594763839/50000000000000000000)
  directionLo := (249815020322434225027/100000000000000000000)
  directionHi := (62453755080608556257/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree026.table
  base := (-121162351953931346486607635224897057969/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1285470)
      previous := (642735)
      next := (642735)
      square := (4429038315559634625233342868975000000000000)
      linear := (-119668731377778700343530658050578750000000000)
      constant := (801411105048541971164013934520409540659115092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree026.table
  base := (-977290400167722766233095457924441062817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (180)
      previous := (90)
      next := (90)
      square := (620183198986156217213938650000000000000)
      linear := (-16775531524198010260850999590000000000000)
      constant := (112463997161278445168015080044575558937183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249815020322434225027/100000000000000000000)
  centralHi := (62453755080608556257/25000000000000000000)
  directionLo := (254762332682534043887/100000000000000000000)
  directionHi := (15922645792658377743/6250000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree027.table
  base := (-816239279714828407065949020338215550413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-777794170433721748155997924931991875000000000)
      constant := (5382541165639821328330944302544747742358777387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree027.table
  base := (-1639485342426684250528412291878348202359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-2943906979011534150204865163785000000000000)
      constant := (20394814563266474885585125276358184153801329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254762332682534043887/100000000000000000000)
  centralHi := (15922645792658377743/6250000000000000000)
  directionLo := (32451923076923076923/12500000000000000000)
  directionHi := (51923076923076923077/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree028.table
  base := (-279837387104213930804910613192456943443/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-21776869600576374042367206735779752500000000000)
      constant := (155690184990439497967275945975863958371819254556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree028.table
  base := (-2244834067915440490006735582122095099121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-3052749130433604566325911396860000000000000)
      constant := (21849334810918670709443394093551365928248551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32451923076923076923/12500000000000000000)
  centralHi := (51923076923076923077/20000000000000000000)
  directionLo := (264379367016683077303/100000000000000000000)
  directionHi := (33047420877085384663/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree029.table
  base := (-2793589290716720155754001045030726009581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-45106593198884521769044938996791448750000000000)
      constant := (333032807514210719269257952958362326595658623513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree029.table
  base := (-174934631510315942898929825369208092079/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-1580795640927837491223478814967500000000000)
      constant := (11684513450529947478139775885928643159509192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264379367016683077303/100000000000000000000)
  centralHi := (33047420877085384663/12500000000000000000)
  directionLo := (134529505573396370849/50000000000000000000)
  directionHi := (269059011146792741699/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree030.table
  base := (-3301901473145203198537552898415208262883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (48276540)
      previous := (24138270)
      next := (24138270)
      square := (166334994517684055925429987745950000000000000)
      linear := (-5184383021846255050372829391335932500000000000)
      constant := (39511451581898932149210607405949613867019990751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree030.table
  base := (-330658724954206820264448180745546612259/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-327043343327774539856800386301000000000000)
      constant := (2495308946976620233854868636640252622528229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134529505573396370849/50000000000000000000)
  centralHi := (269059011146792741699/100000000000000000000)
  directionLo := (17103665229276090137/6250000000000000000)
  directionHi := (273658643668417442193/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree031.table
  base := (-235478010972857511630095077721984264411/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-24106150597174034568832995023627668125000000000)
      constant := (189540727296386975754309655241502154826760462824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree031.table
  base := (-942934080888226157113729487650682974521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-1689637792349907907344525048042500000000000)
      constant := (13300423020270503533398844294949381654611902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17103665229276090137/6250000000000000000)
  centralHi := (273658643668417442193/100000000000000000000)
  directionLo := (69545558372545348527/25000000000000000000)
  directionHi := (278182233490181394109/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree032.table
  base := (-1048554353636783922041078155847563735063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-24882577596039921410988257786243640000000000000)
      constant := (201729900247695516554277491358193265544168167798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree032.table
  base := (-4197780449344534837251625869321274357007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-3488117736121886230810096329160000000000000)
      constant := (28311725541572471131015631042804704633665817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69545558372545348527/25000000000000000000)
  centralHi := (278182233490181394109/100000000000000000000)
  directionLo := (70658357964899368217/25000000000000000000)
  directionHi := (282633431859597472869/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree033.table
  base := (-1146117488278332539521551472308594169793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-950333503515029935301611872179985625000000000)
      constant := (7939466602924333145551000576942360327283922014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree033.table
  base := (-4587572294138379187336769062283143984961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-3596959887543956646931142562235000000000000)
      constant := (30085245872100174490649448093844773666541591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70658357964899368217/25000000000000000000)
  centralHi := (282633431859597472869/100000000000000000000)
  directionLo := (35876950857209854137/12500000000000000000)
  directionHi := (287015606857678833097/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree034.table
  base := (-4825020883428014996606453439724943367/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-26435431593771695095298783311475583750000000000)
      constant := (227444905977927494639565413141181934132534419392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree034.table
  base := (-2471760059777847105194263625048012544019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-1852901019483013531526094397655000000000000)
      constant := (15960500017955062395922763685118135880060789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35876950857209854137/12500000000000000000)
  centralHi := (287015606857678833097/100000000000000000000)
  directionLo := (58266374644396603577/20000000000000000000)
  directionHi := (145665936610991508943/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree035.table
  base := (-5265311422401535047860758548042935469753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-54423717185275163874908092148183111250000000000)
      constant := (481930723174169716853775192603490804071040025269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree035.table
  base := (-1053531405825167923600179402020256110411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-762928838077619495834647005677000000000000)
      constant := (6763728887701172048668896690081701717340541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58266374644396603577/20000000000000000000)
  centralHi := (145665936610991508943/50000000000000000000)
  directionLo := (147792559124417284373/50000000000000000000)
  directionHi := (295585118248834568747/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree036.table
  base := (-5559662396710208031780984405457403429673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (16092180)
      previous := (8046090)
      next := (8046090)
      square := (55444998172561351975143329248650000000000000)
      linear := (-2073206340111368057748837691607965000000000000)
      constant := (18883324918722882376280066068792933300983804127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree036.table
  base := (-5561699418016953319397953359559279272193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-3923486341810167895294281261460000000000000)
      constant := (35777889009103965538487447656444481802999383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147792559124417284373/50000000000000000000)
  centralHi := (295585118248834568747/100000000000000000000)
  directionLo := (299778024386921070033/100000000000000000000)
  directionHi := (149889012193460535017/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree037.table
  base := (-5825328644183311675863712284219941825239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-57529425180738711243529143198646998750000000000)
      constant := (538643450332881956711085835337953026225996320347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree037.table
  base := (-582709631242239520304159748301818189147/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-403232849323223831141532749453500000000000)
      constant := (3779848886227776285612435868815555226034157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299778024386921070033/100000000000000000000)
  centralHi := (149889012193460535017/50000000000000000000)
  directionLo := (303913089024598236011/100000000000000000000)
  directionHi := (75978272256149559003/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree038.table
  base := (-3031769104722131792480405606855865346029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-29541139589235242463919834361939471250000000000)
      constant := (284154395734496452130740287290769099853765857017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree038.table
  base := (-1213014204099723482660068826108747134977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-828234128930861745507274745522000000000000)
      constant := (7976047451789762356771387510556121734188887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303913089024598236011/100000000000000000000)
  centralHi := (75978272256149559003/25000000000000000000)
  directionLo := (307992641885518592619/100000000000000000000)
  directionHi := (15399632094275929631/5000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree039.table
  base := (-6275328056678798366900304421115250618143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (285660)
      previous := (142830)
      next := (142830)
      square := (984230736791029916718520637550000000000000)
      linear := (-39865307808154016181558313115786250000000000)
      constant := (393716826536292641419813483080713026956507059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree039.table
  base := (-6276656293895129197515677483660343170319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (180)
      previous := (90)
      next := (90)
      square := (620183198986156217213938650000000000000)
      linear := (-25148004710511119193239171365000000000000)
      constant := (248656566059694350644286824991964656829681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307992641885518592619/100000000000000000000)
  centralHi := (15399632094275929631/5000000000000000000)
  directionLo := (62403772075338276227/20000000000000000000)
  directionHi := (19501178773543211321/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree040.table
  base := (-6461573801680977135333967101427349019329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-62187987173934032296460719774342830000000000000)
      constant := (630244841825961235569470311327018313898720137917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree040.table
  base := (-6462724011447785721810692824900174919949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-4358854947498449559778466193760000000000000)
      constant := (44226508730173103758132163197991870438528619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62403772075338276227/20000000000000000000)
  centralHi := (19501178773543211321/6250000000000000000)
  directionLo := (78998445794014343287/25000000000000000000)
  directionHi := (315993783176057373149/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree041.table
  base := (-51742303260493987681793452584166334847/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-31870420585832902990385622649787386875000000000)
      constant := (331255826371761235627542028254038089723481063984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree041.table
  base := (-3312005119340440235069588273914173412677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-2233848549460259987949756213417500000000000)
      constant := (23245380031064740841405908487658817193257587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78998445794014343287/25000000000000000000)
  centralHi := (315993783176057373149/100000000000000000000)
  directionLo := (63983864460054329781/20000000000000000000)
  directionHi := (159959661150135824453/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree042.table
  base := (-135205508653043058360042529851125865887/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89401000000000000000000000000000000000000000
      center := (1609218)
      previous := (804609)
      next := (804609)
      square := (5544499817256135197514332924865000000000000)
      linear := (-241828500627398443204006558610395250000000000)
      constant := (2576452662563778110230104535644832122944181565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree042.table
  base := (-3380568191805816792800207949609046378653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-2288269625171295196010279329955000000000000)
      constant := (24407804321001284414369827605457321162007643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63983864460054329781/20000000000000000000)
  centralHi := (159959661150135824453/50000000000000000000)
  directionLo := (32379727385543723529/10000000000000000000)
  directionHi := (323797273855437235291/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree043.table
  base := (-859235354139920404210448028602310654789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-33423274583564676674696148175019330625000000000)
      constant := (364817633868716068633030160384384784612424279988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree043.table
  base := (-6874627057028242704159420779395061555557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-4685381401764660808141604892985000000000000)
      constant := (51200965810569159795437591231627859597110867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32379727385543723529/10000000000000000000)
  centralHi := (323797273855437235291/100000000000000000000)
  directionLo := (327629327642323477551/100000000000000000000)
  directionHi := (20476832977645217347/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree044.table
  base := (-696428217593788426496155309724006268699/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2413827000000000000000000000000000000000000000
      center := (43448886)
      previous := (21724443)
      next := (21724443)
      square := (149701495065915650332886988971355000000000000)
      linear := (-6839940316486112703370282187527060500000000000)
      constant := (76448972474670685089216176923013755307945098927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree044.table
  base := (-1741231287657913055714178075723829567803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-2397111776593365612131325563030000000000000)
      constant := (26823378359565897489902888484550345606082586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327629327642323477551/100000000000000000000)
  centralHi := (20476832977645217347/6250000000000000000)
  directionLo := (2071356723511308411/625000000000000000)
  directionHi := (331417075761809345761/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree045.table
  base := (-3515924676632283884105360616328026521853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-1295412169677646309592839766675973125000000000)
      constant := (14818605232989017289553665290217855464201069947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree045.table
  base := (-1758101141609267884421617753598690233197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-2451532852304400820191848679567500000000000)
      constant := (28076459089124951996960597955641455201179414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2071356723511308411/625000000000000000)
  centralHi := (331417075761809345761/100000000000000000000)
  directionLo := (335162020344872615063/100000000000000000000)
  directionHi := (41895252543109076883/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree046.table
  base := (-7076901769581648364970865581047211343237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45630000000000000000000000000000000000000000
      center := (821340)
      previous := (410670)
      next := (410670)
      square := (2829895936973830819147202059950000000000000)
      linear := (-135170342458080669947682179443732500000000000)
      constant := (1581813563482085532225824754116188293390809569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree046.table
  base := (-707738096330943361561160905812196732793/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-501190785603087205650474359221000000000000)
      constant := (5871939684157531316636711590579988752157983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335162020344872615063/100000000000000000000)
  centralHi := (41895252543109076883/12500000000000000000)
  directionLo := (338865580513578766931/100000000000000000000)
  directionHi := (84716395128394691733/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree047.table
  base := (-7099707442143680226492160933726024650347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-73057965158056448086634398450966436250000000000)
      constant := (874213155301270280895325581331246342776014352031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree047.table
  base := (-3550060414754452063074863154665086553741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-2560375003726471236312894912642500000000000)
      constant := (30673073836296027249497531286866912872417771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338865580513578766931/100000000000000000000)
  centralHi := (84716395128394691733/25000000000000000000)
  directionLo := (171264549332277652423/50000000000000000000)
  directionHi := (342529098664555304847/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree048.table
  base := (-7100492685433037629135438673900098714151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (48276540)
      previous := (24138270)
      next := (24138270)
      square := (166334994517684055925429987745950000000000000)
      linear := (-8290091017309802418993880441799820000000000000)
      constant := (101389497439459998958567283149764281824568559347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree048.table
  base := (-3550424571003017199360228109452408882997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-2614796079437506444373418029180000000000000)
      constant := (32016566325096052408566558930942542898773507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171264549332277652423/50000000000000000000)
  centralHi := (342529098664555304847/100000000000000000000)
  directionLo := (173076923076923076923/50000000000000000000)
  directionHi := (346153846153846153847/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree049.table
  base := (-7079448599947160859426192265322492136307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-76163673153519995455255449501430323750000000000)
      constant := (951655878760091940948298223666229533953781983111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree049.table
  base := (-1769938958176560098532706821147891571649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-2669217155148541652433941145717500000000000)
      constant := (33390159837941724411702446977067325148782638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173076923076923076923/50000000000000000000)
  centralHi := (346153846153846153847/100000000000000000000)
  directionLo := (349741028451407915039/100000000000000000000)
  directionHi := (2185881427821299469/625000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree050.table
  base := (-1759184137839673330958088015071596797279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-38858263575625884569782987513331133750000000000)
      constant := (495831985603654316021499671183907270044603846534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree050.table
  base := (-21990628898223404293268084892866804043/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-544727646171915372098892852451000000000000)
      constant := (6958768165122217405062281469605626323735456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349741028451407915039/100000000000000000000)
  centralHi := (2185881427821299469/625000000000000000)
  directionLo := (176645894912248420543/50000000000000000000)
  directionHi := (353291789824496841087/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree051.table
  base := (-6972492797142143705138793955183544224989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (16092180)
      previous := (8046090)
      next := (8046090)
      square := (55444998172561351975143329248650000000000000)
      linear := (-2935903005517908993476907427847933750000000000)
      constant := (38241830570178486779295123548973108189304258411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree051.table
  base := (-1743180188639319358421555332297874438887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-2778059306570612068554987378792500000000000)
      constant := (36227597849476410829296575221871130939656194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176645894912248420543/50000000000000000000)
  centralHi := (353291789824496841087/100000000000000000000)
  directionLo := (356807217601528316811/100000000000000000000)
  directionHi := (89201804400382079203/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree052.table
  base := (-3443416196658745778811252553215707243667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1285470)
      previous := (642735)
      next := (642735)
      square := (4429038315559634625233342868975000000000000)
      linear := (-239119038895607445290494159991497500000000000)
      constant := (3178260247329277913475276470274538490938704239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree052.table
  base := (-6887028635762870171766883830772681031913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (180)
      previous := (90)
      next := (90)
      square := (620183198986156217213938650000000000000)
      linear := (-33520477896824228125627343140000000000000)
      constant := (446052322517583406871210105099227318968087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356807217601528316811/100000000000000000000)
  centralHi := (89201804400382079203/25000000000000000000)
  directionLo := (360288346061446050337/100000000000000000000)
  directionHi := (180144173030723025169/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree053.table
  base := (-6779852493321287286478319838901514482141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-82375089144447090192497551602358098750000000000)
      constant := (1116831351303150719029104444405473168494304536393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree053.table
  base := (-6780021370719786132645939388998716077061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-5773802915985364969352067223735000000000000)
      constant := (78370605765714009724516556812704841982976691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360288346061446050337/100000000000000000000)
  centralHi := (180144173030723025169/50000000000000000000)
  directionLo := (181868079994016704777/50000000000000000000)
  directionHi := (72747231997606681911/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree054.table
  base := (-6651635133587444082163677119919247074857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (16092180)
      previous := (8046090)
      next := (8046090)
      square := (55444998172561351975143329248650000000000000)
      linear := (-3108442338599217180622521375095927500000000000)
      constant := (42972866314467567869984037764819600798510709343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree054.table
  base := (-6651780410124546458168663488420356277111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-5882645067407435385473113456810000000000000)
      constant := (81418471714512351475467446039659459789168241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181868079994016704777/50000000000000000000)
  centralHi := (72747231997606681911/20000000000000000000)
  directionLo := (73430319584756858303/20000000000000000000)
  directionHi := (91787899480946072879/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree055.table
  base := (-6502249585703358237611667066973392381853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-85480797139910637561118602652821986250000000000)
      constant := (1204559913950088785104455370567734579491776418569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree055.table
  base := (-1625593629194030301256673456555714473493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-2995743609414752900797079844942500000000000)
      constant := (42263214365476797537253144335904481007959366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73430319584756858303/20000000000000000000)
  centralHi := (91787899480946072879/25000000000000000000)
  directionLo := (370535555153801798657/100000000000000000000)
  directionHi := (185267777576900899329/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree056.table
  base := (-791469292822533847838928041059085328241/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-43516825568821205622714564089026965000000000000)
      constant := (624854390244887807336154648468662368707552046772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree056.table
  base := (-1266372348396720381526526914516435633171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-1220065874050315243543041184592000000000000)
      constant := (17538893400873300810463470920878722377994101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370535555153801798657/100000000000000000000)
  centralHi := (185267777576900899329/50000000000000000000)
  directionLo := (373888886446607321017/100000000000000000000)
  directionHi := (186944443223303660509/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree057.table
  base := (-6140198795583603565908988774405932706067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (48276540)
      previous := (24138270)
      next := (24138270)
      square := (166334994517684055925429987745950000000000000)
      linear := (-9842945015041576103304405967031763750000000000)
      constant := (143968207876385933229884648853071578247622212399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree057.table
  base := (-191884096690893609905052565968028095521/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-3104585760836823316918126078017500000000000)
      constant := (45461289126168983417092917824302764529711216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373888886446607321017/100000000000000000000)
  centralHi := (186944443223303660509/50000000000000000000)
  directionLo := (377212408575635211251/100000000000000000000)
  directionHi := (94303102143908802813/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree058.table
  base := (-1185524930141702744803135329723191925943/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-18027871826621191722810035845703563500000000000)
      constant := (268515016894424993225667029946753320896726786139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree058.table
  base := (-37048149669990167617081045753364868117/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-631801367309571704995729838911000000000000)
      constant := (9421075548265398553132519868587151396611632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377212408575635211251/100000000000000000000)
  centralHi := (94303102143908802813/25000000000000000000)
  directionLo := (380506902642488053007/100000000000000000000)
  directionHi := (23781681415155503313/6250000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree059.table
  base := (-5694067124404071738577425964340210525439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-91692213130837732298360704753749761250000000000)
      constant := (1390292336237314705397170640189013030890198654947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree059.table
  base := (-5694135230196140329948329696065676458027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-6426855824517787466078344622185000000000000)
      constant := (97558992792323185620362132841570525678593437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380506902642488053007/100000000000000000000)
  centralHi := (23781681415155503313/6250000000000000000)
  directionLo := (95943279055168779267/25000000000000000000)
  directionHi := (383773116220675117069/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree060.table
  base := (-5439555953331768022126496114234954871439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (16092180)
      previous := (8046090)
      next := (8046090)
      square := (55444998172561351975143329248650000000000000)
      linear := (-3453521004761833554913749269591915000000000000)
      constant := (53291316829773563757683585368532821424538481961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree060.table
  base := (-1359903607726702288279988872852662746287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-3267848987969928941099695427630000000000000)
      constant := (50483642598953254873486039319400799991754994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95943279055168779267/25000000000000000000)
  centralHi := (383773116220675117069/100000000000000000000)
  directionLo := (9675294133412551571/2500000000000000000)
  directionHi := (387011765336502062841/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree061.table
  base := (-1291029061752339162411231607892830732889/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-47398960563150639833490877902106824375000000000)
      constant := (744147339180903801271820986480087097324639237594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree061.table
  base := (-2582083221787765963809602769388468980043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-3322270063680964149160218544167500000000000)
      constant := (52217814246138268120550638048461161242372733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9675294133412551571/2500000000000000000)
  centralHi := (387011765336502062841/100000000000000000000)
  directionLo := (15608941452079249497/4000000000000000000)
  directionHi := (195111768150990618713/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree062.table
  base := (-4867769207786401719853418204314983475711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-96350775124033053351292281329445592500000000000)
      constant := (1538579656932275007396003449990550773100524944003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree062.table
  base := (-4867812284437708649784973448227053926511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-6753382278783998714441483321410000000000000)
      constant := (107964019123689482503368452195832127886419641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15608941452079249497/4000000000000000000)
  centralHi := (195111768150990618713/50000000000000000000)
  directionLo := (49176135926631691921/12500000000000000000)
  directionHi := (393409087413053535369/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree063.table
  base := (-1137633184698537407861711927075056246223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-1813030168921570871029681608419954375000000000)
      constant := (29439267535189386090994792202319401125094085154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree063.table
  base := (-4550569695807546609806881566858208485701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-6862224430206069130562529554485000000000000)
      constant := (111552454093694247501731560758871587765916531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49176135926631691921/12500000000000000000)
  centralHi := (393409087413053535369/100000000000000000000)
  directionLo := (198284525262512307977/50000000000000000000)
  directionHi := (79313810105004923191/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree064.table
  base := (-4212421957300452516289997653294628658481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-99456483119496600719913332379909480000000000000)
      constant := (1641717011775193819388885186910294706389184783213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree064.table
  base := (-4212453656067196990773170617407418733399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-6971066581628139546683575787560000000000000)
      constant := (115200930870944247686248689103898146234055569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198284525262512307977/50000000000000000000)
  centralHi := (79313810105004923191/20000000000000000000)
  directionLo := (99926008128973690011/25000000000000000000)
  directionHi := (79940806503178952009/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree065.table
  base := (-3853449628188326119354416442236587077321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2570940)
      previous := (1285470)
      next := (1285470)
      square := (8858076631119269250466685737950000000000000)
      linear := (-597688385309043635527951821923913750000000000)
      constant := (10027037400857731618786184829460783068962124157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree065.table
  base := (-1926738405107193646400734300129390512071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (90)
      previous := (45)
      next := (45)
      square := (310091599493078108606969325000000000000)
      linear := (-20946475541568668529007757457500000000000)
      constant := (351803098575251086122485083132683109487929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/25000000000000000000)
  centralHi := (79940806503178952009/20000000000000000000)
  directionLo := (80562923329436199057/20000000000000000000)
  directionHi := (201407308323590497643/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree066.table
  base := (-138945061199463197617366086226167741699/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 536406000000000000000000000000000000000000000
      center := (9655308)
      previous := (4827654)
      next := (4827654)
      square := (33266998903536811185085997549190000000000000)
      linear := (-2279159802554669957522986298452741500000000000)
      constant := (38850607728711365796071101311886748259615515515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree066.table
  base := (-69472996666863268114517520669774182849/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-718875088447228037892566825371000000000000)
      constant := (12267800163207521201580340475616290815492595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80562923329436199057/20000000000000000000)
  centralHi := (201407308323590497643/50000000000000000000)
  directionLo := (101475340957718427863/25000000000000000000)
  directionHi := (405901363830873711453/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree067.table
  base := (-3072961763947147854046202179002137277253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-104115045112691921772844908955605311250000000000)
      constant := (1802841070947510619345364415230448769349647722769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree067.table
  base := (-614596347500952944623880813972363879881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-1459518607178870159009342897357000000000000)
      constant := (25301318457765724589589038038205795504300111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101475340957718427863/25000000000000000000)
  centralHi := (405901363830873711453/100000000000000000000)
  directionLo := (204482406905160940427/50000000000000000000)
  directionHi := (81792962762064376171/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree068.table
  base := (-2651463015030829564549086445353167012157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-105667899110423695457155434480837255000000000000)
      constant := (1858260471661288246873387191671018437805546105161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree068.table
  base := (-2651480130768325099901060711098595260827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-7406435187316421211167760719860000000000000)
      constant := (130395218002931416284344002051154337400920237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204482406905160940427/50000000000000000000)
  centralHi := (81792962762064376171/20000000000000000000)
  directionLo := (103001371565521874971/25000000000000000000)
  directionHi := (82401097252417499977/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree069.table
  base := (-220913677228430982983097535961164468809/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-750687902458555409518070153371625000000000)
      constant := (13404295556045006311546516555714160861021279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree069.table
  base := (-1104575717963625209624123202987462225003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-3757638669369245813644403476467500000000000)
      constant := (67171938844465753215371429830347931383974493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103001371565521874971/25000000000000000000)
  centralHi := (82401097252417499977/20000000000000000000)
  directionLo := (415023881825139191099/100000000000000000000)
  directionHi := (4150238818251391911/1000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree070.table
  base := (-872994257463510318275596965513130473389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-54386803552943621412888242765650571250000000000)
      constant := (985833122773741414652853900333127252043185850297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree070.table
  base := (-218250134392160536763929262634832953137/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-3812059745080281021704926593005000000000000)
      constant := (69176285215242286358276566545840102923679388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415023881825139191099/100000000000000000000)
  centralHi := (4150238818251391911/1000000000000000000)
  directionLo := (209010241531578440967/50000000000000000000)
  directionHi := (83604096612631376387/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree071.table
  base := (-252404573896653954731683296447205788293/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-22065292220723803302017402211306617250000000000)
      constant := (405930518865276538011733820603525680304599572689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree071.table
  base := (-631016812896550947007170480956539318547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-3866480820791316229765449709542500000000000)
      constant := (71210647727005457519062657071568657355165557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209010241531578440967/50000000000000000000)
  centralHi := (83604096612631376387/20000000000000000000)
  directionLo := (52624469420648164173/12500000000000000000)
  directionHi := (84199151073037062677/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree072.table
  base := (-378621871232444945981233918950966620157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-2071839168543533151748102529291945000000000000)
      constant := (38675825392166001782686417401476635883191344043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree072.table
  base := (-151450590424725110391239333183402267577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-1568360758600940575130389130432000000000000)
      constant := (29310010421291169104236506599916005016779487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52624469420648164173/12500000000000000000)
  centralHi := (84199151073037062677/20000000000000000000)
  directionLo := (423950147789396209303/100000000000000000000)
  directionHi := (52993768473674526163/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree073.table
  base := (-231654432408663377680845766014810836963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-113432169099082563878708062106996973750000000000)
      constant := (2148192168137129902107923886667768294506533612599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree073.table
  base := (-231662316288375900865743824586881971751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-7950645944426773291772991885235000000000000)
      constant := (150738839836514405178759832159665441946774081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423950147789396209303/100000000000000000000)
  centralHi := (52993768473674526163/12500000000000000000)
  directionLo := (213442046927145318131/50000000000000000000)
  directionHi := (426884093854290636263/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree074.table
  base := (62948455103829626041150475304743338681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-22997004619362867512603717526445783500000000000)
      constant := (441749075696794117150801056844560100292728342187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree074.table
  base := (157367763915999533348999145858140151921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-4029744047924421853947019059155000000000000)
      constant := (77493829089390382250057368683351275685674649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213442046927145318131/50000000000000000000)
  centralHi := (426884093854290636263/100000000000000000000)
  directionLo := (429798012281288645749/100000000000000000000)
  directionHi := (1719192049125154583/400000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree075.table
  base := (176388805927733223729917522978121390717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 536406000000000000000000000000000000000000000
      center := (9655308)
      previous := (4827654)
      next := (4827654)
      square := (33266998903536811185085997549190000000000000)
      linear := (-2589730602101024694385091403499130250000000000)
      constant := (50447871034243061357595472171521217302291971551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree075.table
  base := (881938255455270905876155033877081690607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-8168330247270914124015084351385000000000000)
      constant := (159296506740366726878066098804990851805712583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429798012281288645749/100000000000000000000)
  centralHi := (1719192049125154583/400000000000000000)
  directionLo := (432692307692307692307/100000000000000000000)
  directionHi := (108173076923076923077/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree076.table
  base := (1469948844302200763298794956472594293301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-118090731092277884931639638682692805000000000000)
      constant := (2332418617515021421935650987935206424740215872927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree076.table
  base := (734971952025712228488000706345126754823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-4138586199346492270068065292230000000000000)
      constant := (81832692594802359875312922975677326421565087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432692307692307692307/100000000000000000000)
  centralHi := (108173076923076923077/25000000000000000000)
  directionLo := (10889184281640504371/2500000000000000000)
  directionHi := (435567371265620174841/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree077.table
  base := (1039377521467967919360906734044364642061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-59821792545004829307975082103962374375000000000)
      constant := (1197769318679631211593792358220199034129445927447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree077.table
  base := (1039375408454687928264692422100241647787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-4193007275057527478128588408767500000000000)
      constant := (84047146623255284972433930509552753338476003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10889184281640504371/2500000000000000000)
  centralHi := (435567371265620174841/100000000000000000000)
  directionLo := (438423581352999912451/100000000000000000000)
  directionHi := (109605895338249978113/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree078.table
  base := (677090302486090518040386146197579428119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (47610)
      previous := (23805)
      next := (23805)
      square := (164038456131838319453086772925000000000000)
      linear := (-13280346163460599638424357849348750000000000)
      constant := (269506273576228150721703482826681492159949902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree078.table
  base := (135417879774728870177066470902500561871/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (62018319898615621721393865000000000000)
      linear := (-5026542426945044599040368669000000000000)
      constant := (102120254837119490472972776970055001123742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438423581352999912451/100000000000000000000)
  centralHi := (109605895338249978113/25000000000000000000)
  directionLo := (441261304060914071829/100000000000000000000)
  directionHi := (44126130406091407183/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree079.table
  base := (1679383075049218547795494817397342589389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-61374646542736602992285607629194318125000000000)
      constant := (1262172730261066164589803642659992477360360831703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree079.table
  base := (671752611845627476331883436415133779613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-1720739770591839157699853856737000000000000)
      constant := (35426439454950198782786136699660282608754597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441261304060914071829/100000000000000000000)
  centralHi := (44126130406091407183/10000000000000000000)
  directionLo := (111020223449572012687/25000000000000000000)
  directionHi := (444080893798288050749/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree080.table
  base := (2014984427121510458823766086188951349501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-62151073541602489834440870391810290000000000000)
      constant := (1295016129259879588083838884602067292869111950327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree080.table
  base := (805993242306278151991494538905055710479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-1742508200876253240924063103352000000000000)
      constant := (36348238575629188119692281725234954415070951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111020223449572012687/25000000000000000000)
  centralHi := (444080893798288050749/100000000000000000000)
  directionLo := (446882693793163486751/100000000000000000000)
  directionHi := (13965084181036358961/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree081.table
  base := (2360984235170160145870927896195635805331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-2330648168165495432466523450163935625000000000)
      constant := (49195826751719755816508194186638024493663646731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree081.table
  base := (4721966211159937555838353312276452240789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-8821383155803336620741361749835000000000000)
      constant := (186410217342746475355857251356325345428693341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446882693793163486751/100000000000000000000)
  centralHi := (13965084181036358961/3125000000000000000)
  directionLo := (8993340731607632101/2000000000000000000)
  directionHi := (449667036580381605051/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree082.table
  base := (5434764279019068259849732220968119604651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-127407855078668527037502791834084467500000000000)
      constant := (2723972617005017455743414687081318397459685909377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree082.table
  base := (5434762348003195297505294267392791170623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-8930225307225407036862407982910000000000000)
      constant := (191139270548543909748384558442971881707835287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8993340731607632101/2000000000000000000)
  centralHi := (449667036580381605051/100000000000000000000)
  directionLo := (113108561115563379333/25000000000000000000)
  directionHi := (452434244462253517333/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree083.table
  base := (1542088918232088245812918908265503907349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-64480354538200150360906658679658205625000000000)
      constant := (1396113087145085535826336815951057729308922779246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree083.table
  base := (154208850566346499999769191574076439917/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-903906745864747745298345421598500000000000)
      constant := (19592835239423840940258381767153638173383892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113108561115563379333/25000000000000000000)
  centralHi := (452434244462253517333/100000000000000000000)
  directionLo := (455184629944024039767/100000000000000000000)
  directionHi := (56898078743003004971/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree084.table
  base := (3461371069652048347941734687557493507313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (24138270)
      previous := (12069135)
      next := (12069135)
      square := (83167497258842027962714993872975000000000000)
      linear := (-7250753504118448578117991271363797500000000000)
      constant := (158963073067255771459855212813813145868641868539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree084.table
  base := (6922740729160025257659528161748257111503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-9147909610069547869104500449060000000000000)
      constant := (200777462794324102135902672580025455451844007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455184629944024039767/100000000000000000000)
  centralHi := (56898078743003004971/12500000000000000000)
  directionLo := (457918496145794525279/100000000000000000000)
  directionHi := (2861990600911215783/625000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree085.table
  base := (1924480811312074719341489455067927460683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-66033208535931924045217184204890149375000000000)
      constant := (1465650019360687508857735013615788296273369877682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree085.table
  base := (3848961020232092865194485623980615277509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-4628375880745809142612773341067500000000000)
      constant := (102843300838314134772930201502635536481899021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457918496145794525279/100000000000000000000)
  centralHi := (2861990600911215783/625000000000000000)
  directionLo := (11515903429811042307/2500000000000000000)
  directionHi := (460636137192441692281/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree086.table
  base := (1698779725059787707688319801853803655759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-26723854213919124354948978787002448500000000000)
      constant := (600424068788064474445693131383206605910719779693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree086.table
  base := (8493897596110578624163705308442960552829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-9365593912913688701346592915210000000000000)
      constant := (210655768980233887720268407764649360333428101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11515903429811042307/2500000000000000000)
  centralHi := (460636137192441692281/100000000000000000000)
  directionLo := (463337838582952227129/100000000000000000000)
  directionHi := (46333783858295222713/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree087.table
  base := (232766699273352722789335977667397039079/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89401000000000000000000000000000000000000000
      center := (1609218)
      previous := (804609)
      next := (804609)
      square := (5544499817256135197514332924865000000000000)
      linear := (-500637500249360723922427479482385875000000000)
      constant := (11384430481936027559886730729764211979669056716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree087.table
  base := (4655333545933757179794585346169255754359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-4737218032167879558733819574142500000000000)
      constant := (107842482326862900560104503138582916722486671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463337838582952227129/100000000000000000000)
  centralHi := (46333783858295222713/10000000000000000000)
  directionLo := (466023877540485925781/100000000000000000000)
  directionHi := (233011938770242962891/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree088.table
  base := (5074115510854708462584870239964602383039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-68362489532529584571682972492738065000000000000)
      constant := (1573163848319961258271751939158973750026443880253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree088.table
  base := (10148230270966389354358279581091159878559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-9583278215757829533588685381360000000000000)
      constant := (220774188653710115740272300701484406019476471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466023877540485925781/100000000000000000000)
  centralHi := (233011938770242962891/50000000000000000000)
  directionLo := (58586815418047791061/12500000000000000000)
  directionHi := (468694523344382328489/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree089.table
  base := (11006587557774509693620730941958507196071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-138277833062790942827676470510708073750000000000)
      constant := (3219714742961226880595912621192008878604257973717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree089.table
  base := (2751646729176385424071173447883595939663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-4846060183589949974854865807217500000000000)
      constant := (112961720471782125358649399942324967927606094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58586815418047791061/12500000000000000000)
  centralHi := (468694523344382328489/100000000000000000000)
  directionLo := (942700075290472607/200000000000000000)
  directionHi := (471350037645236303501/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree090.table
  base := (2971434348388533387427095311641557696663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-2589457167787457713184944371035926250000000000)
      constant := (60999210530346184731349326514392810752403737726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree090.table
  base := (11885736846206340006114267480048022746297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-9800962518601970365830777847510000000000000)
      constant := (231132721492381717348194553179090615844124193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (942700075290472607/200000000000000000)
  centralHi := (471350037645236303501/100000000000000000000)
  directionLo := (236995337382043029861/50000000000000000000)
  directionHi := (473990674764086059723/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree091.table
  base := (6392840186206260819855406311820471871079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1285470)
      previous := (642735)
      next := (642735)
      square := (4429038315559634625233342868975000000000000)
      linear := (-418294500172350562710939412902875625000000000)
      constant := (9967620039332047804843603516590338577078371357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree091.table
  base := (12785679905142014498994087316148233155039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (180)
      previous := (90)
      next := (90)
      square := (620183198986156217213938650000000000000)
      linear := (-58637897455763554922791858465000000000000)
      constant := (1398828581503439594907215492496773233155039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236995337382043029861/50000000000000000000)
  centralHi := (473990674764086059723/100000000000000000000)
  directionLo := (476616681976681905629/100000000000000000000)
  directionHi := (47661668197668190563/10000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree092.table
  base := (6853208181074050572771217321499754988101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (410670)
      previous := (205335)
      next := (205335)
      square := (1414947968486915409573601029975000000000000)
      linear := (-135100562434769625596037851688472500000000000)
      constant := (3256152510972334312209805865020471819510704863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree092.table
  base := (6853207981643849516242903096739737413819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-5009323410723055599036435156830000000000000)
      constant := (120865683633327485456300657191134015622935411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476616681976681905629/100000000000000000000)
  centralHi := (47661668197668190563/10000000000000000000)
  directionLo := (479228299783735087649/100000000000000000000)
  directionHi := (9584565995674701753/2000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree093.table
  base := (7323972625594659591905847207795094370993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (24138270)
      previous := (12069135)
      next := (12069135)
      square := (83167497258842027962714993872975000000000000)
      linear := (-8027180502984335420273254033979769375000000000)
      constant := (195656595461826232308528616644114717910427185579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree093.table
  base := (7323972455381878692545702664408242160173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-5063744486434090807096958273367500000000000)
      constant := (123560366225766548473303538227832805425069237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479228299783735087649/100000000000000000000)
  centralHi := (9584565995674701753/2000000000000000000)
  directionLo := (481825762167982666337/100000000000000000000)
  directionHi := (240912881083991333169/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree094.table
  base := (15610266945382489967827264007553694321239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-146042103051449811249229098136867792500000000000)
      constant := (3599483658179388886842327703782147893021103371653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree094.table
  base := (7805133327432197286141967853879073954201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-5118165562145126015157481389905000000000000)
      constant := (126285062906524195144475825034356813498259969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481825762167982666337/100000000000000000000)
  centralHi := (240912881083991333169/50000000000000000000)
  directionLo := (242204648419423055797/50000000000000000000)
  directionHi := (96881859367769222319/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree095.table
  base := (4148345341319885325846670339246511467961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-73797478524590792466769811831049868125000000000)
      constant := (1839002088008252958212048635682204298289191543494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree095.table
  base := (8296690558690188713959161910217702779353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-5172586637856161223218004506442500000000000)
      constant := (129039773668991745267278258899122104269710657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242204648419423055797/50000000000000000000)
  centralHi := (96881859367769222319/20000000000000000000)
  directionLo := (60872390683175957391/12500000000000000000)
  directionHi := (486979125465407659129/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree096.table
  base := (703891537753914905424085771545593986883/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 178802000000000000000000000000000000000000000
      center := (3218436)
      previous := (1609218)
      next := (1609218)
      square := (11088999634512270395028665849730000000000000)
      linear := (-1104798600347506360132223327313568000000000000)
      constant := (27832446456758653105179412173922786240106635415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree096.table
  base := (8798644116169445745587943157392936490539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-5227007713567196431278527622980000000000000)
      constant := (131824498507594496019771661078879406266901091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60872390683175957391/12500000000000000000)
  centralHi := (486979125465407659129/100000000000000000000)
  directionLo := (244767731949189527677/50000000000000000000)
  directionHi := (97907092779675811071/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree097.table
  base := (4655497031134160163633225867029215296301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-75350332522322566151080337356281811875000000000)
      constant := (1918805972490310846356696735492024009556892457854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree097.table
  base := (18621987944095551656396004583800341717017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-10562857578556463278678101479035000000000000)
      constant := (269278474835260993721055418602672882750175873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244767731949189527677/50000000000000000000)
  centralHi := (97907092779675811071/20000000000000000000)
  directionLo := (492078522381691753943/100000000000000000000)
  directionHi := (61509815297711469243/12500000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree098.table
  base := (1966748035964400893731818784129640119077/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2413827000000000000000000000000000000000000000
      center := (43448886)
      previous := (21724443)
      next := (21724443)
      square := (149701495065915650332886988971355000000000000)
      linear := (-15225351904237690598647120023779556750000000000)
      constant := (391869919585597250625953100746656926991586277679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree098.table
  base := (19667480205723706691360337199729894480617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-10671699729978533694799147712110000000000000)
      constant := (274967980790268891520847907431696852167224273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492078522381691753943/100000000000000000000)
  centralHi := (61509815297711469243/12500000000000000000)
  directionLo := (6182606321928694719/1250000000000000000)
  directionHi := (494608505754295577521/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree099.table
  base := (1036688255446926414594423428876253144181/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89401000000000000000000000000000000000000000
      center := (1609218)
      previous := (804609)
      next := (804609)
      square := (5544499817256135197514332924865000000000000)
      linear := (-569653233481883998780673058381583375000000000)
      constant := (14817192682190217968624769030957149162342101162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree099.table
  base := (20733764977654723552475232156572968861319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-10780541881400604110920193945185000000000000)
      constant := (280717514873525586454553461455816456737562911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6182606321928694719/1250000000000000000)
  centralHi := (494608505754295577521/100000000000000000000)
  directionLo := (6214070170533925233/1250000000000000000)
  directionHi := (497125613642714018641/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree100.table
  base := (21820842338495101814696669508607768519007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-155359227037840453355092251288259455000000000000)
      constant := (4083440429904891413637465035433785210935929109789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree100.table
  base := (5455210556632538011542529573154749782009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-5444692016411337263520620089130000000000000)
      constant := (143263538539696750219729327074351305426319042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6214070170533925233/1250000000000000000)
  centralHi := (497125613642714018641/100000000000000000000)
  directionLo := (99926008128973690011/20000000000000000000)
  directionHi := (62453755080608556257/12500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree101.table
  base := (143304450123200888273196475839727312261/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2413827000000000000000000000000000000000000000
      center := (43448886)
      previous := (21724443)
      next := (21724443)
      square := (149701495065915650332886988971355000000000000)
      linear := (-15691208103557222703940277681349139875000000000)
      constant := (416709441292753090872025660035350842417787275552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree101.table
  base := (358261123816136893237890404242403719669/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-5499113092122372471581143205667500000000000)
      constant := (146198333701560410717840651932455731815969952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/20000000000000000000)
  centralHi := (62453755080608556257/12500000000000000000)
  directionLo := (502121976505650296559/100000000000000000000)
  directionHi := (6276524706320628707/1250000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree102.table
  base := (12028687064240862104571681799240781001737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (24138270)
      previous := (12069135)
      next := (12069135)
      square := (83167497258842027962714993872975000000000000)
      linear := (-8803607501850222262428516796595741250000000000)
      constant := (236200220733393609804136522408975426046383868611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree102.table
  base := (24057374047068580448276193338465146939353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-11107068335666815359283332644410000000000000)
      constant := (298326285840703268434236955181683109832750657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502121976505650296559/100000000000000000000)
  centralHi := (6276524706320628707/1250000000000000000)
  directionLo := (20184064251387578553/4000000000000000000)
  directionHi := (252300803142344731913/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree103.table
  base := (25206828644488924837047405712946503489333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-160017789031035774408023827863955286250000000000)
      constant := (4336969110676516906695043575453002540732833707391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree103.table
  base := (12603414287538210336320437869806022820869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-5607955243544442887702189438742500000000000)
      constant := (152157966194383700228753101960907530356726861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20184064251387578553/4000000000000000000)
  centralHi := (252300803142344731913/50000000000000000000)
  directionLo := (507069110516738819017/100000000000000000000)
  directionHi := (253534555258369409509/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree104.table
  base := (26377075550620244243510066821369633327883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2570940)
      previous := (1285470)
      next := (1285470)
      square := (8858076631119269250466685737950000000000000)
      linear := (-956039307862529870368842327746670000000000000)
      constant := (26172720859837382672114716539337789972822152889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree104.table
  base := (13188537745722506552705088164085248282461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (90)
      previous := (45)
      next := (45)
      square := (310091599493078108606969325000000000000)
      linear := (-33505185321038331927590015120000000000000)
      constant := (918241440959976665944643352944085248282461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507069110516738819017/100000000000000000000)
  centralHi := (253534555258369409509/50000000000000000000)
  directionLo := (254762332682534043887/50000000000000000000)
  directionHi := (20380986614602723511/4000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree105.table
  base := (27568114832464134194270518358693770419903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (16092180)
      previous := (8046090)
      next := (8046090)
      square := (55444998172561351975143329248650000000000000)
      linear := (-6041611000981456362097958478311821250000000000)
      constant := (167046893224974084700438031459781603058372248103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree105.table
  base := (27568114782021000320486317875879412791851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-11433594789933026607646471343635000000000000)
      constant := (316475309805425488924576178949964245761822819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254762332682534043887/50000000000000000000)
  centralHi := (20380986614602723511/4000000000000000000)
  directionLo := (511968442768236003683/100000000000000000000)
  directionHi := (127992110692059000921/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree106.table
  base := (28779946477889298052851709468393803848593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-164676351024231095460955404439651117500000000000)
      constant := (4598197985932581901302225348013199433331187695411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree106.table
  base := (28779946434893623670785041629598597991359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-11542436941355097023767517576710000000000000)
      constant := (322645040669614609752009141157124663060539671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511968442768236003683/100000000000000000000)
  centralHi := (127992110692059000921/25000000000000000000)
  directionLo := (257200305290293382931/50000000000000000000)
  directionHi := (514400610580586765863/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree107.table
  base := (30012570476688659039646434907855660112923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-166229205021962869145265929964883061250000000000)
      constant := (4686985431862724397236893669536211556475584086321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree107.table
  base := (30012570440044157539900259836597487207597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-11651279092777167439888563809785000000000000)
      constant := (328874799635346310942415711086370600338083893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257200305290293382931/50000000000000000000)
  centralHi := (514400610580586765863/100000000000000000000)
  directionLo := (258410666353397844009/50000000000000000000)
  directionHi := (516821332706795688019/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree108.table
  base := (31265986820278776330081607830780707372013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (16092180)
      previous := (8046090)
      next := (8046090)
      square := (55444998172561351975143329248650000000000000)
      linear := (-6214150334062764549243572425559815000000000000)
      constant := (176912164994222549388910186425192561644765334213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree108.table
  base := (15632993394525001053198992157465839182689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-5880060622099618928004805021430000000000000)
      constant := (167582293350598586562986772367476726821874441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258410666353397844009/50000000000000000000)
  centralHi := (516821332706795688019/100000000000000000000)
  directionLo := (519230769230769230769/100000000000000000000)
  directionHi := (51923076923076923077/10000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree109.table
  base := (6508039100289215807186443076307509081881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-33866982603485283302777396203069389750000000000)
      constant := (973425410971804579583371584347778416248027068587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree109.table
  base := (8135048868708729488510518405184643955749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-5934481697810654136065328137967500000000000)
      constant := (170757200932985655920669367099430222157043162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519230769230769230769/100000000000000000000)
  centralHi := (51923076923076923077/10000000000000000000)
  directionLo := (130407269134796570481/25000000000000000000)
  directionHi := (20865163061567451277/4000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree110.table
  base := (33835196514132631041196458771482996993699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-170887767015158190198197506540578892500000000000)
      constant := (4958481231893143780724662060347696112403059476073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree110.table
  base := (33835196491458212645217292880163897767819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-11977805547043378688251702509010000000000000)
      constant := (347924245128664750066554304784410198722761411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130407269134796570481/25000000000000000000)
  centralHi := (20865163061567451277/4000000000000000000)
  directionLo := (524016407439950480553/100000000000000000000)
  directionHi := (262008203719975240277/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree111.table
  base := (140603959413021094513629916773266057917/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 268203000000000000000000000000000000000000000
      center := (4827654)
      previous := (2413827)
      next := (2413827)
      square := (16633499451768405592542998774595000000000000)
      linear := (-1916006900143221820916755911842342625000000000)
      constant := (56118788732601129068516450821248459987506578775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree111.table
  base := (17575494916968404738295421911701961611259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-6043323849232724552186374371042500000000000)
      constant := (177197058244217673919378506792002944012302771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524016407439950480553/100000000000000000000)
  centralHi := (262008203719975240277/50000000000000000000)
  directionLo := (263196455637903736543/50000000000000000000)
  directionHi := (526392911275807473087/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree112.table
  base := (36487575514552950347202423016085018449981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-173993475010621737566818557591042780000000000000)
      constant := (5143756316971610951133903446541445361830062287287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree112.table
  base := (36487575498095074251140191590497427635629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-12195489849887519520493794975160000000000000)
      constant := (360924015944577422978650052206314065270421301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263196455637903736543/50000000000000000000)
  centralHi := (526392911275807473087/100000000000000000000)
  directionLo := (264379367016683077303/50000000000000000000)
  directionHi := (528758734033366154607/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree113.table
  base := (37844953494457827099614779993199966411907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-175546329008353511251129083116274723750000000000)
      constant := (5237677224997059651349738470705955919503841738089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree113.table
  base := (37844953480438074209436298388803244078711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-12304332001309589936614841208235000000000000)
      constant := (367513943496500331849889913264378373249302159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264379367016683077303/50000000000000000000)
  centralHi := (528758734033366154607/100000000000000000000)
  directionLo := (531114018447749104723/100000000000000000000)
  directionHi := (132778504611937276181/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree114.table
  base := (7844624757997300625832672626001177641033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 178802000000000000000000000000000000000000000
      center := (3218436)
      previous := (1609218)
      next := (1609218)
      square := (11088999634512270395028665849730000000000000)
      linear := (-1311845800045076184706960064011160500000000000)
      constant := (39499657111135157803823488387008480313535991233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree114.table
  base := (7844624755608923442389236072850739803777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-2482634830546332070547177488262000000000000)
      constant := (74832779828742078596179104497372275026838313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531114018447749104723/100000000000000000000)
  centralHi := (132778504611937276181/25000000000000000000)
  directionLo := (266729452051542250251/50000000000000000000)
  directionHi := (533458904103084500503/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree115.table
  base := (10155521599662046269847082513968550867229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (410670)
      previous := (205335)
      next := (205335)
      square := (1414947968486915409573601029975000000000000)
      linear := (-168858258037634270907136232671775625000000000)
      constant := (5130515852537011874648352967138038616308081854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree115.table
  base := (40622086388476988225142166265118802620373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-12522016304153730768856933674385000000000000)
      constant := (380873882885795632531000703432220702642843037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266729452051542250251/50000000000000000000)
  centralHi := (533458904103084500503/100000000000000000000)
  directionLo := (535793527529039710701/100000000000000000000)
  directionHi := (267896763764519855351/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree116.table
  base := (525523016479589788275745275753023938921/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2413827000000000000000000000000000000000000000
      center := (43448886)
      previous := (21724443)
      next := (21724443)
      square := (149701495065915650332886988971355000000000000)
      linear := (-18020489100154883230406065969197055500000000000)
      constant := (552457341093478607463926129373651381310810885336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree116.table
  base := (21020920654852390245897976556174385918387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-6315429227787900592488989953730000000000000)
      constant := (193821947361206455879116936448498471220207403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535793527529039710701/100000000000000000000)
  centralHi := (267896763764519855351/50000000000000000000)
  directionLo := (538118022293585483397/100000000000000000000)
  directionHi := (269059011146792741699/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree117.table
  base := (43482388547417498703849307003508451378037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (95220)
      previous := (47610)
      next := (47610)
      square := (328076912263676638906173545850000000000000)
      linear := (-39832948717791059826511327025466250000000000)
      constant := (1232065883596529164107952542911859759841481573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree117.table
  base := (1087059713501015606671300587554370208863/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (62018319898615621721393865000000000000)
      linear := (-7538284382838977278756820201500000000000)
      constant := (233416529380637316672000383692279980835452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538118022293585483397/100000000000000000000)
  centralHi := (269059011146792741699/50000000000000000000)
  directionLo := (108086503818433815101/20000000000000000000)
  directionHi := (270216259546084537753/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree118.table
  base := (44943728084367622208974569494583797061433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-183310598997012379672681710742434442500000000000)
      constant := (5720115419729232649938110872015923031078157634091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree118.table
  base := (8988745615617191666170234949191394547/2000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-1284854275841994201722007237361000000000000)
      constant := (40136400267815173593725242480670922839221500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108086503818433815101/20000000000000000000)
  centralHi := (270216259546084537753/50000000000000000000)
  directionLo := (542737145833464784879/100000000000000000000)
  directionHi := (6784214322918309811/1250000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree119.table
  base := (1450808122751060891763621162614346910107/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-92431726497372076678496118133833193125000000000)
      constant := (2909584894783369639587265385869384572196069341824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree119.table
  base := (9285171984537055698688144692965422604567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-2591476981968402486668223721337000000000000)
      constant := (81662819759368328766955919701247281420171823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542737145833464784879/100000000000000000000)
  centralHi := (6784214322918309811/1250000000000000000)
  directionLo := (545032027721861085031/100000000000000000000)
  directionHi := (68129003465232635629/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree120.table
  base := (47928784077441470247693672277122820485737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (48276540)
      previous := (24138270)
      next := (24138270)
      square := (166334994517684055925429987745950000000000000)
      linear := (-20712922999163991893478084643655370000000000000)
      constant := (657675526262347662694833280795582759322736120611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree120.table
  base := (47928784072887541277623379808143411193759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-13066227061264082849462164839760000000000000)
      constant := (415324223009186062520649627553776236491745271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545032027721861085031/100000000000000000000)
  centralHi := (68129003465232635629/12500000000000000000)
  directionLo := (17103665229276090137/3125000000000000000)
  directionHi := (109463457467366976877/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree121.table
  base := (49452500531790613530040907212015819451187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-187969160990207700725613287318130273750000000000)
      constant := (6019845260110471672317411923927424757973087862649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree121.table
  base := (12363125131978401736132226735913018105003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-6587534606343076632791605536417500000000000)
      constant := (211197187657526658689496720962338912619491014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17103665229276090137/3125000000000000000)
  centralHi := (109463457467366976877/20000000000000000000)
  directionLo := (549593044709355295061/100000000000000000000)
  directionHi := (274796522354677647531/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree122.table
  base := (5099700929042926033448708065157422341621/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2413827000000000000000000000000000000000000000
      center := (43448886)
      previous := (21724443)
      next := (21724443)
      square := (149701495065915650332886988971355000000000000)
      linear := (-18952201498793947440992381284336221750000000000)
      constant := (612146636081319330321242736712181564345482993567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree122.table
  base := (25498504643564389949799126731300187625287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-6641955682054111840852128652955000000000000)
      constant := (214762277857168072427165280965430981708673503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549593044709355295061/100000000000000000000)
  centralHi := (274796522354677647531/50000000000000000000)
  directionLo := (551859417395451662757/100000000000000000000)
  directionHi := (275929708697725831379/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree123.table
  base := (13140577588207287136069571139719771081711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-3538423499734652742485821080899891875000000000)
      constant := (115258204416074420807000891132747880309733340222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree123.table
  base := (52562310350019651312777183825802525384337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-13392753515530294097825303538985000000000000)
      constant := (436714764206947778854381821766206251789952953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551859417395451662757/100000000000000000000)
  centralHi := (275929708697725831379/50000000000000000000)
  directionLo := (554116520547073444023/100000000000000000000)
  directionHi := (69264565068384180503/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree124.table
  base := (27074201859282983941785275264483888806833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-96313861491701510889272431946913052500000000000)
      constant := (3163637646536961860907032283672044360304431279891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree124.table
  base := (54148403716174572707598157429518765807939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-13501595666952364513946349772060000000000000)
      constant := (443965000792818650786624207068678671421541691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554116520547073444023/100000000000000000000)
  centralHi := (69264565068384180503/12500000000000000000)
  directionLo := (69545558372545348527/12500000000000000000)
  directionHi := (556364466980362788217/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree125.table
  base := (13938822346825643873202169295801683881201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-97090288490567397731427694709529024375000000000)
      constant := (3215731562315047246691612576285371133079409282454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree125.table
  base := (55755289385267193889494671195797038109553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-13610437818374434930067396005135000000000000)
      constant := (451275265471893607468175978818105324440514457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69545558372545348527/12500000000000000000)
  centralHi := (556364466980362788217/100000000000000000000)
  directionLo := (558603367241454358439/100000000000000000000)
  directionHi := (13965084181036358961/2500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree126.table
  base := (57382967358774844784260462073079818104607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (16092180)
      previous := (8046090)
      next := (8046090)
      square := (55444998172561351975143329248650000000000000)
      linear := (-7249386332550613672117256109047777500000000000)
      constant := (242092834560588647496172000659579696474619970407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree126.table
  base := (14345741839260646724996637800352059112201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-6859639984898252673094221119105000000000000)
      constant := (229322779122064783037026993810730245979923938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558603367241454358439/100000000000000000000)
  centralHi := (13965084181036358961/2500000000000000000)
  directionLo := (22433333186796439261/4000000000000000000)
  directionHi := (280416664834955490763/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree127.table
  base := (59031437632779736920142890679406200214763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-197286284976598342831476440469521936250000000000)
      constant := (6642405518590830588225631902470026642975488228001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree127.table
  base := (2361257505252222089585054334869220960293/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-2765624424243715152461897694257000000000000)
      constant := (93215175821898707577770323255026616711447585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22433333186796439261/4000000000000000000)
  centralHi := (280416664834955490763/50000000000000000000)
  directionLo := (11261089209197962521/2000000000000000000)
  directionHi := (563054460459898126051/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree128.table
  base := (60700700209165248198836555647230634289119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-198839138974330116515786965994753880000000000000)
      constant := (6749160080994538900231119937357477220274201248413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree128.table
  base := (3035035010395538327120019190944999153249/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-1393696427264064617843053470436000000000000)
      constant := (47356622806796096326371254797707409713798162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11261089209197962521/2000000000000000000)
  centralHi := (563054460459898126051/100000000000000000000)
  directionLo := (565266863719194945737/100000000000000000000)
  directionHi := (282633431859597472869/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree129.table
  base := (12478151017564388125167337148377973335719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 536406000000000000000000000000000000000000000
      center := (9655308)
      previous := (4827654)
      next := (4827654)
      square := (33266998903536811185085997549190000000000000)
      linear := (-4453155399379153115557722033777462750000000000)
      constant := (152372671563261205645047703423021111980997342957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree129.table
  base := (12478151017350896803461173253438610497431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-2809161284812543318910316187487000000000000)
      constant := (96223321023902861831991463214337250174065839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565266863719194945737/100000000000000000000)
  centralHi := (282633431859597472869/50000000000000000000)
  directionLo := (567470641526134671837/100000000000000000000)
  directionHi := (283735320763067335919/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree130.table
  base := (4006350141792238033373430915663555706673/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1285470)
      previous := (642735)
      next := (642735)
      square := (4429038315559634625233342868975000000000000)
      linear := (-597469961449093680131384665814253750000000000)
      constant := (20607206913157686428213455586027389513642283672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree130.table
  base := (8012700283470943603355885997490032018651/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (90)
      previous := (45)
      next := (45)
      square := (310091599493078108606969325000000000000)
      linear := (-41877658507351440859978186895000000000000)
      constant := (1445937900189768900121447172371210128074604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567470641526134671837/100000000000000000000)
  centralHi := (283735320763067335919/50000000000000000000)
  directionLo := (71208236748070308957/12500000000000000000)
  directionHi := (569665893984562471657/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree131.table
  base := (16458310437920568152433240060170281883787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-101748850483762718784359271285224855625000000000)
      constant := (3537278614948031284803756094952708705200985595698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree131.table
  base := (13166648350181902687396626990106568690777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-2852698145381371485358734680717000000000000)
      constant := (99279488700367372974747023615863135108741313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71208236748070308957/12500000000000000000)
  centralHi := (569665893984562471657/100000000000000000000)
  directionLo := (571852719276894492783/100000000000000000000)
  directionHi := (35740794954805905799/6250000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree132.table
  base := (6758567353682112518334814507957057760169/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89401000000000000000000000000000000000000000
      center := (1609218)
      previous := (804609)
      next := (804609)
      square := (5544499817256135197514332924865000000000000)
      linear := (-759446499871323004640848400354376500000000000)
      constant := (26610126296640737580823551408562670983316868769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree132.table
  base := (33792836768081844968738205194477540521123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-7186166439164463921457359818330000000000000)
      constant := (252063952416298209400592541833851704348069787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571852719276894492783/100000000000000000000)
  centralHi := (35740794954805905799/6250000000000000000)
  directionLo := (35876950857209854137/6250000000000000000)
  directionHi := (574031213715357666193/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree133.table
  base := (69358897624092278082251333676625980898141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-206603408962988984937339593620913598750000000000)
      constant := (7295766547238107531547360068959297349835604495607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree133.table
  base := (69358897623532988314869527954757575097903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-14481175029750998259035765869735000000000000)
      constant := (511918394256421041811124742735099655191545607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35876950857209854137/6250000000000000000)
  centralHi := (574031213715357666193/100000000000000000000)
  directionLo := (288100735895742965131/50000000000000000000)
  directionHi := (576201471791485930263/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree134.table
  base := (71152914013512187517474719699844664929849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-208156262960720758621650119146145542500000000000)
      constant := (7407654571331427446229022962792586948482372622123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree134.table
  base := (14230582802607283687699286573618473306311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-2918003436234613735031362420562000000000000)
      constant := (103953782354662789314294306404742021988766559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288100735895742965131/50000000000000000000)
  centralHi := (576201471791485930263/100000000000000000000)
  directionLo := (9036931034749138229/1562500000000000000)
  directionHi := (578363586223944846657/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree135.table
  base := (72967722705110850035797651488250128913079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (16092180)
      previous := (8046090)
      next := (8046090)
      square := (55444998172561351975143329248650000000000000)
      linear := (-7767004331794538233554097950791758750000000000)
      constant := (278533265643445603605254456143515927314020675679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree135.table
  base := (36483861352353075874078604391324672852413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-7349429666297569545638929167942500000000000)
      constant := (263839728691640285027775832835504182212057797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9036931034749138229/1562500000000000000)
  centralHi := (578363586223944846657/100000000000000000000)
  directionLo := (29025882400237654713/5000000000000000000)
  directionHi := (580517648004753094261/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree136.table
  base := (14960664739785856017580988495069612606151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-42252394191236861198054234039321886000000000000)
      constant := (1526799470072603617334871059872417071288267649877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree136.table
  base := (74803323698585054863440742041164741219153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-14807701484017209507398904568960000000000000)
      constant := (535650031086328156722075665468916841266036857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29025882400237654713/5000000000000000000)
  centralHi := (580517648004753094261/100000000000000000000)
  directionLo := (58266374644396603577/10000000000000000000)
  directionHi := (582663746443966035771/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree137.table
  base := (19164929248754348427174994178675015486913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-106407412476958039837290847860920686875000000000)
      constant := (3874226052650754151449630322036954664367801242102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree137.table
  base := (38329858497362310518044802132843707133247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-7458271817719639961759975401017500000000000)
      constant := (271840316441232704465294013010780899005518743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58266374644396603577/10000000000000000000)
  centralHi := (582663746443966035771/100000000000000000000)
  directionLo := (18275061537902607537/3125000000000000000)
  directionHi := (116960393842576688237/20000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree138.table
  base := (628295220747457876643010447394166444137/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1014000000000000000000000000000000000000000
      center := (18252)
      previous := (9126)
      next := (9126)
      square := (62886576377196240425493379110000000000000)
      linear := (-9005153495133285165254871718003500000000000)
      constant := (330340787111474044931604476554216403429436475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree138.table
  base := (39268451296591618466225928808754985059459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-7512692893430675169820498517555000000000000)
      constant := (275885631385851097013850784917100842475048571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18275061537902607537/3125000000000000000)
  centralHi := (116960393842576688237/20000000000000000000)
  directionLo := (293466201192920256017/50000000000000000000)
  directionHi := (117386480477168102407/20000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree139.table
  base := (40217440247118244344928365583819541512701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-107960266474689813521601373386152630625000000000)
      constant := (3989964173012281704947431482191308509677072266727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree139.table
  base := (20108720123506182998932833444584811072057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-7567113969141710377881021634092500000000000)
      constant := (279960960377024649594658872230522478642355266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293466201192920256017/50000000000000000000)
  centralHi := (117386480477168102407/20000000000000000000)
  directionLo := (294527565240319284693/50000000000000000000)
  directionHi := (589055130480638569387/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree140.table
  base := (82353650697497242185119089922698501209071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-217473386947111400727513272297537205000000000000)
      constant := (8096949831809441548148630743608147426952988224717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree140.table
  base := (82353650697317165878365153773260972852077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-15243070089705491171883089501260000000000000)
      constant := (568132606829518226496698423355331104412001013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294527565240319284693/50000000000000000000)
  centralHi := (589055130480638569387/100000000000000000000)
  directionLo := (591170236497669137493/100000000000000000000)
  directionHi := (295585118248834568747/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree141.table
  base := (84293213203284944120697810612153569491179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (16092180)
      previous := (8046090)
      next := (8046090)
      square := (55444998172561351975143329248650000000000000)
      linear := (-8112082997957154607845325845287746250000000000)
      constant := (304252847946053485414374354733555713492643393779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree141.table
  base := (42146606601565908195296139842567252501693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-7675956120563780794002067867167500000000000)
      constant := (288201660499060510949886995554531678172786117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591170236497669137493/100000000000000000000)
  centralHi := (295585118248834568747/50000000000000000000)
  directionLo := (593277801957782664657/100000000000000000000)
  directionHi := (296638900978891332329/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree142.table
  base := (21563392002918135441184448630396192810983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-110289547471287474048067161674000546250000000000)
      constant := (4166779767113373583049358934805828206418088323882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree142.table
  base := (86253568011542336282348471029350833804753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-15460754392549632004125181967410000000000000)
      constant := (584734063259870132713283591080342790913003257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593277801957782664657/100000000000000000000)
  centralHi := (296638900978891332329/50000000000000000000)
  directionLo := (148844476734737691181/25000000000000000000)
  directionHi := (23815116277558030589/4000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree143.table
  base := (44117357561367380595089290559436398398641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1285470)
      previous := (642735)
      next := (642735)
      square := (4429038315559634625233342868975000000000000)
      linear := (-657195115208008052604866416784713125000000000)
      constant := (25009312872365476638144754582130887324421539403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree143.table
  base := (44117357561312026065528618439468652255139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (90)
      previous := (45)
      next := (45)
      square := (310091599493078108606969325000000000000)
      linear := (-46063895100507995326172272782500000000000)
      constant := (1754807200043722748901810048232281152255139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148844476734737691181/25000000000000000000)
  centralHi := (23815116277558030589/4000000000000000000)
  directionLo := (149367657527942157203/25000000000000000000)
  directionHi := (597470630111768628813/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree144.table
  base := (45118327268273755068011545920144007951349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-4142311165519231397495469896267870000000000000)
      constant := (158770213785962576798530542964694499454858551949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree144.table
  base := (22559163634113345697593920437645766666529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-7839219347696886418183637216780000000000000)
      constant := (300787816031429202966313328719444269133286802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149367657527942157203/25000000000000000000)
  centralHi := (597470630111768628813/100000000000000000000)
  directionLo := (599556048773842140067/100000000000000000000)
  directionHi := (149889012193460535017/25000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree145.table
  base := (18451877250637476744736534140703458735369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-45047531387154053829813179984739384750000000000)
      constant := (1738978182994855236750803132781525322024757047163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree145.table
  base := (92259386253107358384959763114244397512689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-15787280846815843252488320666635000000000000)
      constant := (610086458604123501215795031301897928179644441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599556048773842140067/100000000000000000000)
  centralHi := (149889012193460535017/25000000000000000000)
  directionLo := (120326847776620443493/20000000000000000000)
  directionHi := (300817119441551108733/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree146.table
  base := (18860582054546251330302542008469283406557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4827654000000000000000000000000000000000000000
      center := (86897772)
      previous := (43448886)
      next := (43448886)
      square := (299402990131831300665773977942710000000000000)
      linear := (-45358102186700408566675285089785773500000000000)
      constant := (1763409172491321555163106636362699195801149263639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree146.table
  base := (11787863784082902976941078929314883685883/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-7948061499118956834304683449855000000000000)
      constant := (309328656619293314683269227160028111371656908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120326847776620443493/20000000000000000000)
  centralHi := (300817119441551108733/50000000000000000000)
  directionLo := (1886578984656521911/312500000000000000)
  directionHi := (603705275090087011521/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree147.table
  base := (96367226595255948055189035018418535155453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (48276540)
      previous := (24138270)
      next := (24138270)
      square := (166334994517684055925429987745950000000000000)
      linear := (-25371484992359312946409661219351201250000000000)
      constant := (993339598543239927934334760425951630563985460959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree147.table
  base := (48183613297599056626390662358506138087213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-8002482574829992042365206566392500000000000)
      constant := (313644097983130413029852531958155349836738997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1886578984656521911/312500000000000000)
  centralHi := (603705275090087011521/100000000000000000000)
  directionLo := (60576923076923076923/10000000000000000000)
  directionHi := (605769230769230769231/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree148.table
  base := (98452335220837947386261452399993444079169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-229896218928965590201997476499392755000000000000)
      constant := (9063922488272115542837820765389840937016288269763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree148.table
  base := (12306541902598598027565514823912125425881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-8056903650541027250425729682930000000000000)
      constant := (317989553393579531658409060336029596787895556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60576923076923076923/10000000000000000000)
  centralHi := (605769230769230769231/100000000000000000000)
  directionLo := (607826178049196472023/100000000000000000000)
  directionHi := (75978272256149559003/12500000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree149.table
  base := (100558236149553191488318262825987766686333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-231449072926697363886308002024624698750000000000)
      constant := (9188644166605659648505305163448658959889358626391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree149.table
  base := (20111647229902280331776820663322533604551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-3244529890500824983394501119787000000000000)
      constant := (128946009140258842602551820568222633179169119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607826178049196472023/100000000000000000000)
  centralHi := (75978272256149559003/12500000000000000000)
  directionLo := (152469046960571930891/25000000000000000000)
  directionHi := (121975237568457544713/20000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree150.table
  base := (25671232345369221148068633388879806535569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-4314850498600539584641083843515863750000000000)
      constant := (172485581886851355526195612260498020371297808338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree150.table
  base := (10268492938144136386936189018134843616267/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-1633149160392619533309355183201000000000000)
      constant := (65354101270867901746048161373121038571149123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152469046960571930891/25000000000000000000)
  centralHi := (121975237568457544713/20000000000000000000)
  directionLo := (611919329872973819193/100000000000000000000)
  directionHi := (305959664936486909597/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree151.table
  base := (104832414916683354253745589651101197095283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-234554780922160911254929053075088586250000000000)
      constant := (9440654254125235606426182734494214829085603178041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree151.table
  base := (52416207458326581759156865483109269183063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-8220166877674132874607299032542500000000000)
      constant := (331206003904663032960299929946645778991937647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611919329872973819193/100000000000000000000)
  centralHi := (305959664936486909597/50000000000000000000)
  directionLo := (61395567270556046073/10000000000000000000)
  directionHi := (613955672705560460731/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree152.table
  base := (26750173188811484338441129572084724865589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-118053817459946342469619789300160265000000000000)
      constant := (4783971331655811947541848817224226884086260198206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree152.table
  base := (10700069275522027795105672788979012687409/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169000000000000000000000000000000000000000
      center := (3042)
      previous := (1521)
      next := (1521)
      square := (10481096062866040070915563185000000000000)
      linear := (-1654917590677033616533564429816000000000000)
      constant := (67134303100324777606447243160229453144172121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61395567270556046073/10000000000000000000)
  centralHi := (613955672705560460731/100000000000000000000)
  directionLo := (615985283771037185239/100000000000000000000)
  directionHi := (15399632094275929631/2500000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree153.table
  base := (109189762897236891210893584779851992235681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (16092180)
      previous := (8046090)
      next := (8046090)
      square := (55444998172561351975143329248650000000000000)
      linear := (-8802240330282387356427781634279721250000000000)
      constant := (359114320349974536335318554041569432996924617081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree153.table
  base := (27297440724303770994057641463882534175931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-8329009029096203290728345265617500000000000)
      constant := (340167041145228189786379717803452609051464678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615985283771037185239/100000000000000000000)
  centralHi := (15399632094275929631/2500000000000000000)
  directionLo := (309004114696565624913/50000000000000000000)
  directionHi := (618008229393131249827/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree154.table
  base := (111399625342727325634783481765918252056427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-239213342915356232307860629650784417500000000000)
      constant := (9825086212538473011114392410979781382075359016129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree154.table
  base := (27849906335677198261388433194282909309261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-8383430104807238498788868382155000000000000)
      constant := (344692580835481955590400648182268873346530218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309004114696565624913/50000000000000000000)
  centralHi := (618008229393131249827/100000000000000000000)
  directionLo := (124004914962719290611/20000000000000000000)
  directionHi := (9687883981462444579/1562500000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree155.table
  base := (56815140045893576205505479976240177159241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-120383098456544002996085577588008180625000000000)
      constant := (4977470676289637120110857680723473665982852975307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree155.table
  base := (28407570022942850849955560494612527561557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-8437851180518273706849391498692500000000000)
      constant := (349248134572391100295646270063461846815806266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124004914962719290611/20000000000000000000)
  centralHi := (9687883981462444579/1562500000000000000)
  directionLo := (622034384216764173309/100000000000000000000)
  directionHi := (62203438421676417331/10000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree156.table
  base := (115881727144485049263622310250919007484719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (285660)
      previous := (142830)
      next := (142830)
      square := (984230736791029916718520637550000000000000)
      linear := (-159315615325982761128521815056705000000000000)
      constant := (6630934956983485828086897631016185339878249053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree156.table
  base := (3621303973264739571768890597056298353847/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (90)
      previous := (45)
      next := (45)
      square := (310091599493078108606969325000000000000)
      linear := (-50250131693664549792366358670000000000000)
      constant := (2093690546484978895759651560497900773661552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622034384216764173309/100000000000000000000)
  centralHi := (62203438421676417331/10000000000000000000)
  directionLo := (62403772075338276227/10000000000000000000)
  directionHi := (624037720753382762271/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree157.table
  base := (118153966500888435811309498599604054443237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-243871904908551553360792206226480248750000000000)
      constant := (10217218363516458863305688589030910554791742937999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree157.table
  base := (118153966500877063894364040787052558679179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-17093386663880688245940875463535000000000000)
      constant := (716898568372397314191990696018747507416781251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62403772075338276227/10000000000000000000)
  centralHi := (624037720753382762271/100000000000000000000)
  directionLo := (78254330820471293029/12500000000000000000)
  directionHi := (626034646563770344233/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree158.table
  base := (30111749540265864857281435217051211635343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (217244430)
      previous := (108622215)
      next := (108622215)
      square := (748507475329578251664434944856775000000000000)
      linear := (-122712379453141663522551365875856096250000000000)
      constant := (5174820117206582332449074908557930825915585175322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree158.table
  base := (4817879926442151870200406438635697360283/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (6084)
      previous := (3042)
      next := (3042)
      square := (20962192125732080141831126370000000000000)
      linear := (-3440445763060551732412384339322000000000000)
      constant := (145237952025243346152388123302955664269439135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78254330820471293029/12500000000000000000)
  centralHi := (626034646563770344233/100000000000000000000)
  directionLo := (314012611400152518247/50000000000000000000)
  directionHi := (125605044560061007299/20000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree159.table
  base := (61380411062537494630785924137677046613541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-4573659498222501865359504764387854375000000000)
      constant := (194128105227076961707222554456887217226328428941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree159.table
  base := (15345102765633347406672068436421705787889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-8655535483362414539091483964842500000000000)
      constant := (367770489986696043502979441091436385612612964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314012611400152518247/50000000000000000000)
  centralHi := (125605044560061007299/20000000000000000000)
  directionLo := (315004754824637809807/50000000000000000000)
  directionHi := (126001901929855123923/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree160.table
  base := (125095438392986616914432596998717682984809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-248530466901746874413723782802176080000000000000)
      constant := (10617050707063586164316309608625661508566172554043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree160.table
  base := (62547719196489820728674568537727930448379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-8709956559073449747152007081380000000000000)
      constant := (372476113956967068202759108163676020245776051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315004754824637809807/50000000000000000000)
  centralHi := (126001901929855123923/20000000000000000000)
  directionLo := (78998445794014343287/12500000000000000000)
  directionHi := (631987566352114746297/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree161.table
  base := (15931355870607582823760636036930442942381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (410670)
      previous := (205335)
      next := (205335)
      square := (1414947968486915409573601029975000000000000)
      linear := (-236373649243363561529332994638381875000000000)
      constant := (10162608042360686003274260994492773721928088012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree161.table
  base := (127450846964854736274316062777676298156379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-17528755269568969910425060395835000000000000)
      constant := (754423503947853416601967213435277919388428051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78998445794014343287/12500000000000000000)
  centralHi := (631987566352114746297/100000000000000000000)
  directionLo := (316979725613017940873/50000000000000000000)
  directionHi := (633959451226035881747/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree162.table
  base := (64913523920379092815518663979477603357173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (8046090)
      previous := (4023045)
      next := (4023045)
      square := (27722499086280675987571664624325000000000000)
      linear := (-4659929164763155958932311738011851250000000000)
      constant := (201627471991191892598576695989172428545859623373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree162.table
  base := (16228380980094143856881943293961269182519/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-8818798710495520163273053314455000000000000)
      constant := (381977404037580125661893696491509067967382844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316979725613017940873/50000000000000000000)
  centralHi := (633959451226035881747/100000000000000000000)
  directionLo := (127185044336818862791/20000000000000000000)
  directionHi := (158981305421023578489/25000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree163.table
  base := (132224041020738998605009229493045654219967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-253189028894942195466655359377871911250000000000)
      constant := (11024583243183999768084131618004651241256007783709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree163.table
  base := (132224041020734721410818308970101238792949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-17746439572413110742667152861985000000000000)
      constant := (773546140295864752890680126848742734356008381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127185044336818862791/20000000000000000000)
  centralHi := (158981305421023578489/25000000000000000000)
  directionLo := (637884934254691757597/100000000000000000000)
  directionHi := (318942467127345878799/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree164.table
  base := (134641826504861684206856725071737645319291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-254741882892673969150965884903103855000000000000)
      constant := (11162138575796659903237714246133199732063128236657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree164.table
  base := (67320913252429025369007959574203950424681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-8927640861917590579394099547530000000000000)
      constant := (391598750304988412587619485055785467621771089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637884934254691757597/100000000000000000000)
  centralHi := (318942467127345878799/50000000000000000000)
  directionLo := (63983864460054329781/10000000000000000000)
  directionHi := (639838644600543297811/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree165.table
  base := (27416080858636722874442689655016862057899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 536406000000000000000000000000000000000000000
      center := (9655308)
      previous := (4827654)
      next := (4827654)
      square := (33266998903536811185085997549190000000000000)
      linear := (-5695438597564572063006142453963017750000000000)
      constant := (251123321896944024260248093214324344915452185497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree165.table
  base := (137080404293180527861660634494076733915381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-17964123875257251574909245328135000000000000)
      constant := (792908889017506166922690994307164593031699389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63983864460054329781/10000000000000000000)
  centralHi := (639838644600543297811/100000000000000000000)
  directionLo := (641786407537124678253/100000000000000000000)
  directionHi := (320893203768562339127/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree166.table
  base := (139539774385760971098387433394694248291017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-257847590888137516519586935953567742500000000000)
      constant := (11439815971881598947126497524028849318738310692059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree166.table
  base := (69769887192879174653473305173691764714827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-9036483013339660995515145780605000000000000)
      constant := (401340152759231137672897005844015158236805763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641786407537124678253/100000000000000000000)
  centralHi := (320893203768562339127/50000000000000000000)
  directionLo := (40233017315663576851/6250000000000000000)
  directionHi := (643728277050617229617/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree167.table
  base := (142019936782648768552760309437017407976699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (434488860)
      previous := (217244430)
      next := (217244430)
      square := (1497014950659156503328869889713550000000000000)
      linear := (-259400444885869290203897461478799686250000000000)
      constant := (11579938035354146264166322529685713184898858917073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree167.table
  base := (17752492097830817698876555231517257337881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (15210)
      previous := (7605)
      next := (7605)
      square := (52405480314330200354577815925000000000000)
      linear := (-9090904089050696203575668897142500000000000)
      constant := (406255875056427224962972222416735978460407556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40233017315663576851/6250000000000000000)
  centralHi := (643728277050617229617/100000000000000000000)
  directionLo := (645664306315367058491/100000000000000000000)
  directionHi := (161416076578841764623/25000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree168.table
  base := (14452089148390087612019028512755461622293/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89401000000000000000000000000000000000000000
      center := (1609218)
      previous := (804609)
      next := (804609)
      square := (5544499817256135197514332924865000000000000)
      linear := (-966493699568892829215585137051969000000000000)
      constant := (43410798799186122497060308692623839274494616493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree168.table
  base := (144520891483898984596424535788465702414381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30420)
      previous := (15210)
      next := (15210)
      square := (104810960628660400709155631850000000000000)
      linear := (-18290650329523462823272384027360000000000000)
      constant := (822403222800691796363296016489330703708030389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell104.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645664306315367058491/100000000000000000000)
  centralHi := (161416076578841764623/25000000000000000000)
  directionLo := (647594547710874470581/100000000000000000000)
  directionHi := (323797273855437235291/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree169.table
  base := (147042638489570042100825281510145010289421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2570940)
      previous := (1285470)
      next := (1285470)
      square := (8858076631119269250466685737950000000000000)
      linear := (-1553290845451673595103659837451263750000000000)
      constant := (70193780432899684630280953442642051299151300143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree169.table
  base := (147042638489568435546331989537744475170611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (180)
      previous := (90)
      next := (90)
      square := (620183198986156217213938650000000000000)
      linear := (-108872736573642208517120889115000000000000)
      constant := (4925175879183332725612786533213369475170611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell104.Kernel169
