import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell161.Parameters
import ForestUnimodality.BinomialMassData.Q49_89.Batch000_049
import ForestUnimodality.BinomialMassData.Q49_89.Batch050_099
import ForestUnimodality.BinomialMassData.Q49_89.Batch100_149
import ForestUnimodality.BinomialMassData.Q99_179.Batch000_049
import ForestUnimodality.BinomialMassData.Q99_179.Batch050_099
import ForestUnimodality.BinomialMassData.Q99_179.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree000.table
  base := (365263181596042659518452917/12500000000000000000000000)
  polynomial :=
    { denominator := 445000000000000000000000000000000000000000
      center := (1617)
      previous := (0)
      next := (1320)
      square := (39543480801838481533683200470000000000000)
      linear := (-157091704378989690249479592250000000000000)
      constant := (13003369264819118678856923845200000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree000.table
  base := (365263181596042659518452917/12500000000000000000000000)
  polynomial :=
    { denominator := 895000000000000000000000000000000000000000
      center := (3267)
      previous := (0)
      next := (2640)
      square := (79531270376731328028419021170000000000000)
      linear := (-315948484088080388254571314750000000000000)
      constant := (26152843802276654421521228857200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree001.table
  base := (82829173233148743673179294831857399159243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-17856422808310253622504637356310000000000000)
      constant := (664854160058445223728965035555622458740363803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree001.table
  base := (82542815574226243157241267505135912749099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-72301970186359192447195231531910000000000000)
      constant := (2680387924023208846421646743166539780393881059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24858765878532948431/50000000000000000000)
  directionHi := (49717531757065896863/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree002.table
  base := (20042595657835036686016122880536633419841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-43463367853780849625611182004740000000000000)
      constant := (833111257999666849410465276142493366592802805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree002.table
  base := (12453240178865384344040465867080939775567/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-88049161720951995396822197723570000000000000)
      constant := (1676033555272366359877114311205981565395768988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24858765878532948431/50000000000000000000)
  centralHi := (49717531757065896863/100000000000000000000)
  directionLo := (8788900962319705701/12500000000000000000)
  directionHi := (70311207698557645609/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree003.table
  base := (8123066683813615677529418576916765871861/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-25606945045470596003106544648430000000000000)
      constant := (290064793630593856036901668801850809884043924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree003.table
  base := (12903376074907592883945105734192099549407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-207592706511089596692898327830460000000000000)
      constant := (2333242828753595626294622180843885308312748435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8788900962319705701/12500000000000000000)
  centralHi := (70311207698557645609/100000000000000000000)
  directionLo := (1076416137876966119/1250000000000000000)
  directionHi := (86113291030157289521/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree004.table
  base := (44917697406389907360609184474387404547163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-58964412328101534386814996588980000000000000)
      constant := (451510160923891383468776267894982631418078123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree004.table
  base := (44569536517366164684456537443347108691987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-239087089580275202592152260213780000000000000)
      constant := (1817633168061275541617147785479644709599955467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1076416137876966119/1250000000000000000)
  centralHi := (86113291030157289521/100000000000000000000)
  directionLo := (3977402540565271749/4000000000000000000)
  directionHi := (49717531757065896863/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree005.table
  base := (16318219518774933035027762199863778871317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-33357467282630938383708451940550000000000000)
      constant := (194413718483656975468760933792120992439701957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree005.table
  base := (1618867571157686736209192244173105859283/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-135290736324730404245703096298550000000000000)
      constant := (783962615215879973916718359612504848372866030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3977402540565271749/4000000000000000000)
  centralHi := (49717531757065896863/50000000000000000000)
  directionLo := (27792945170575976389/25000000000000000000)
  directionHi := (111171780682303905557/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree006.table
  base := (244981818623733187582398947113818512853/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-37232728401211109574009405586610000000000000)
      constant := (181614283461079587648900385326207822015430650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree006.table
  base := (24299179340321397546980364751730237421191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-302075855718646414390660124980420000000000000)
      constant := (1467453064838697230845153211877748537212380831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27792945170575976389/25000000000000000000)
  centralHi := (111171780682303905557/100000000000000000000)
  directionLo := (3805705752357182261/3125000000000000000)
  directionHi := (121782584075429832353/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree007.table
  base := (18678643127490272841726152144803634077051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-82215979039582561528620718465340000000000000)
      constant := (360263407098983345296215286301029585524320971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree007.table
  base := (9259525550878628250639809424164235261719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-166785119393916010144957028681870000000000000)
      constant := (729015601599327555019727867718666262020738479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3805705752357182261/3125000000000000000)
  centralHi := (121782584075429832353/100000000000000000000)
  directionLo := (16442528103644064359/12500000000000000000)
  directionHi := (131540224829152514873/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree008.table
  base := (14244355153631727958716685990426567912683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-89966501276742903909222625757460000000000000)
      constant := (372537960010296709066966540099608844436362043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree008.table
  base := (14111067264052533278363575642681325434937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-365064621857017626189167989747060000000000000)
      constant := (1509992901445372919626709841632592348260816417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16442528103644064359/12500000000000000000)
  centralHi := (131540224829152514873/100000000000000000000)
  directionLo := (8788900962319705701/6250000000000000000)
  directionHi := (140622415397115291217/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree009.table
  base := (2675456817383985269218948101881295316691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-48858511756951623144912266524790000000000000)
      constant := (198071643024517500025461710962883480407018822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree009.table
  base := (10587017557326487889188519069537205723753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-396559004926203232088421922130380000000000000)
      constant := (1607695414321601869617965824016801608594769873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8788900962319705701/6250000000000000000)
  centralHi := (140622415397115291217/100000000000000000000)
  directionLo := (37288148817799422647/25000000000000000000)
  directionHi := (149152595271197690589/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree010.table
  base := (7777724466920145812444899178463784107673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-105467545751063588670426440341700000000000000)
      constant := (428914298614590425722334281243611633916877833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree010.table
  base := (1919209609978507571442582863932562902093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-214026693997694418993837927256850000000000000)
      constant := (871242817944425404892882284112026495891923626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37288148817799422647/25000000000000000000)
  centralHi := (149152595271197690589/100000000000000000000)
  directionLo := (157220639994081437583/100000000000000000000)
  directionHi := (9826289999630089849/6250000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree011.table
  base := (212446513836549910083368992721647313109/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-113218067988223931051028347633820000000000000)
      constant := (469576636336088007733134708908864209178409725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree011.table
  base := (208861236668885334167088826886961514901/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-459547771064574443886929786897020000000000000)
      constant := (1909269079345344058372617522646288347473573525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157220639994081437583/100000000000000000000)
  centralHi := (9826289999630089849/6250000000000000000)
  directionLo := (164894398340766614483/100000000000000000000)
  directionHi := (41223599585191653621/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree012.table
  base := (3200526061611761610956123864030254852571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-120968590225384273431630254925940000000000000)
      constant := (517325396145535357642125715215223648687214891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree012.table
  base := (780127044775926891740439809607751050023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-245521077066880024893091859640170000000000000)
      constant := (1052411421377610109914790831691403902787573886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164894398340766614483/100000000000000000000)
  centralHi := (41223599585191653621/25000000000000000000)
  directionLo := (1076416137876966119/625000000000000000)
  directionHi := (172226582060314579041/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree013.table
  base := (1376874581545161612735875492657892078679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-128719112462544615812232162218060000000000000)
      constant := (571614508006245322275039186517583163155216359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree013.table
  base := (326342254734786339003215878980445969103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-261268268601472827842718825831830000000000000)
      constant := (1163477641504559474033404879784944938592058446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1076416137876966119/625000000000000000)
  centralHi := (172226582060314579041/100000000000000000000)
  directionLo := (44814777509902584277/25000000000000000000)
  directionHi := (179259110039610337109/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree014.table
  base := (-104806703812719629633153463400197164597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-68234817349852479096417034755090000000000000)
      constant := (316024666667378308536337661456987038259227163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree014.table
  base := (-68359093250984713847251418888932395519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-277015460136065630792345792023490000000000000)
      constant := (1287039387334712688410315528167339434230351442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44814777509902584277/25000000000000000000)
  centralHi := (179259110039610337109/100000000000000000000)
  directionLo := (186025969950993626101/100000000000000000000)
  directionHi := (93012984975496813051/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree015.table
  base := (-1596767291888870447939758741886238667201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-144220156936865300573435976802300000000000000)
      constant := (698330225564651724017907699116519103517100879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree015.table
  base := (-1653601737406737719805556511236373894121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-585525303341316867483945516430300000000000000)
      constant := (2844985572590973412310315862034475344058469039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186025969950993626101/100000000000000000000)
  centralHi := (93012984975496813051/50000000000000000000)
  directionLo := (3851103450193091839/2000000000000000000)
  directionHi := (192555172509654591951/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree016.table
  base := (-2814334899156898301607793310887376306039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-151970679174025642954037884094420000000000000)
      constant := (770221552151041541865667350014221092279865081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree016.table
  base := (-2864804361166316541258798546350696678091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-617019686410502473383199448813620000000000000)
      constant := (3138724786824294185129694968510137327737286269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3851103450193091839/2000000000000000000)
  centralHi := (192555172509654591951/100000000000000000000)
  directionLo := (198870127028263587451/100000000000000000000)
  directionHi := (49717531757065896863/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree017.table
  base := (-60722764104861091311126583225555888931/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-79860600705592992667319895693270000000000000)
      constant := (423766839510431309900844221815371897720881568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree017.table
  base := (-1965471190189923641011327531157590975007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-324257034739844039641226690598470000000000000)
      constant := (1727265348595349104217774799950899627569800713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198870127028263587451/100000000000000000000)
  centralHi := (49717531757065896863/25000000000000000000)
  directionLo := (204990634879383090851/100000000000000000000)
  directionHi := (51247658719845772713/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree018.table
  base := (-4832083707514591555123487702184981559843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-167471723648346327715241698678660000000000000)
      constant := (930111747416402349815745934245032761064483597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree018.table
  base := (-48715335315498740289359311904737818567/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-340004226274436842590853656790130000000000000)
      constant := (1895888967947453733570738800498034777764737650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204990634879383090851/100000000000000000000)
  centralHi := (51247658719845772713/25000000000000000000)
  directionLo := (8437344923826917473/4000000000000000000)
  directionHi := (105466811547836468413/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree019.table
  base := (-5667923733579053164299987131430709636941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-175222245885506670095843605970780000000000000)
      constant := (1017828162542747979143971129051497348965790339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree019.table
  base := (-285132769345667990284801967757197584453/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-355751417809029645540480622981790000000000000)
      constant := (2074975680722438714502595090152696321965414270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8437344923826917473/4000000000000000000)
  centralHi := (105466811547836468413/50000000000000000000)
  directionLo := (1354460604070777657/625000000000000000)
  directionHi := (216713696651324425121/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree020.table
  base := (-6407120792630170724629117256400669719223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-182972768122667012476445513262900000000000000)
      constant := (1110577228067220427769065700806050295154034617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree020.table
  base := (-3218809896071493560292483239364159525619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-371498609343622448490107589173450000000000000)
      constant := (2264312224496704836889412097424532964639641621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1354460604070777657/625000000000000000)
  centralHi := (216713696651324425121/100000000000000000000)
  directionLo := (222343561364607811113/100000000000000000000)
  directionHi := (111171780682303905557/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree021.table
  base := (-3530381934187380452969741939800424324217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-95361645179913677428523710277510000000000000)
      constant := (604135554074939000424658631473520838927877143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree021.table
  base := (-7087482124589029788410512066495834041143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-774491601756430502879469110730220000000000000)
      constant := (4927442973194824078162122940678766981487737137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222343561364607811113/100000000000000000000)
  centralHi := (111171780682303905557/50000000000000000000)
  directionLo := (113917176321562648801/50000000000000000000)
  directionHi := (227834352643125297603/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree022.table
  base := (-7638085514184072856092613381224544148303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-198473812596987697237649327847140000000000000)
      constant := (1310836671735467033884514665016960385801291937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree022.table
  base := (-1915360045886882289652724833731661973231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-402992992412808054389361521556770000000000000)
      constant := (2673056113680938090638868153857627637431411058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113917176321562648801/50000000000000000000)
  centralHi := (227834352643125297603/100000000000000000000)
  directionLo := (9327835779714549091/4000000000000000000)
  directionHi := (58298973623215931819/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree023.table
  base := (-2036695293956509979281507927748422468253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-103112167417074019809125617569630000000000000)
      constant := (709106481599029863436189331984029491257935974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree023.table
  base := (-4083577161668350756033964262806640503033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-418740183947400857338988487748430000000000000)
      constant := (2892193383040928007634965267208832431642319647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9327835779714549091/4000000000000000000)
  centralHi := (58298973623215931819/25000000000000000000)
  directionLo := (238436906061837849903/100000000000000000000)
  directionHi := (14902306628864865619/6250000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree024.table
  base := (-4296634643545712914623677796363590606589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-106987428535654190999426571215690000000000000)
      constant := (765174571061799720113362363865483998805208531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree024.table
  base := (-8611008354726769595985395887002229714513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-868974750963987320577230907880180000000000000)
      constant := (6242062045673874873095548785189521557717288967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238436906061837849903/100000000000000000000)
  centralHi := (14902306628864865619/6250000000000000000)
  directionLo := (3805705752357182261/1562500000000000000)
  directionHi := (48713033630171932941/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree025.table
  base := (-8982905234741886824164945606093622662497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-221725379308468724379455049723500000000000000)
      constant := (1647202788493547094936190932154132414890361263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree025.table
  base := (-8998324181104868741558557401128427842479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-900469134033172926476484840263500000000000000)
      constant := (6718967547031505551607763863110444043499130361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3805705752357182261/1562500000000000000)
  centralHi := (48713033630171932941/20000000000000000000)
  directionLo := (124293829392664742157/50000000000000000000)
  directionHi := (49717531757065896863/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree026.table
  base := (-1864031686289383714442240117262731485791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-229475901545629066760056957015620000000000000)
      constant := (1768738500090147615796074346063769519505247445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree026.table
  base := (-9333539372277202758198283143128261910487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-931963517102358532375738772646820000000000000)
      constant := (7214961085980587474549242080102987360126086033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124293829392664742157/50000000000000000000)
  centralHi := (49717531757065896863/20000000000000000000)
  directionLo := (126755332298473991171/50000000000000000000)
  directionHi := (253510664596947982343/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree027.table
  base := (-9608759381964882621561477154528502031471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-237226423782789409140658864307740000000000000)
      constant := (1894926727585210020983277969663819735408718209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree027.table
  base := (-4810177284177760967481217714676228548327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-481728950085772069137496352515070000000000000)
      constant := (3864962045155650025454140234844478961083054593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126755332298473991171/50000000000000000000)
  centralHi := (253510664596947982343/100000000000000000000)
  directionLo := (258339873090471868561/100000000000000000000)
  directionHi := (129169936545235934281/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree028.table
  base := (-1970364417249152305938525178585828873273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-244976946019949751521260771599860000000000000)
      constant := (2025742804985130498660027669492748247474022835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree028.table
  base := (-1232732010185824665148064395323167868529/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-497476141620364872087123318706730000000000000)
      constant := (4131878835748074294746592164721121513297849244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258339873090471868561/100000000000000000000)
  centralHi := (129169936545235934281/50000000000000000000)
  directionLo := (52616089931661005949/20000000000000000000)
  directionHi := (131540224829152514873/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree029.table
  base := (-502597302139479644042951149239361798253/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-126363734128555046950931339445990000000000000)
      constant := (1080583070831145125560722265901430151960379870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree029.table
  base := (-1006061798706045160867037944418058822933/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-513223333154957675036750284898390000000000000)
      constant := (4408189676792780686617901095989184886272018735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52616089931661005949/20000000000000000000)
  centralHi := (131540224829152514873/50000000000000000000)
  directionLo := (26773710231574334981/10000000000000000000)
  directionHi := (267737102315743349811/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree030.table
  base := (-5105650657328105881124935028699389821633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-130238995247135218141232293092050000000000000)
      constant := (1150589774273596162320951445252172133222845007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree030.table
  base := (-10218787193597462846764651781063969174773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1057941049379100955972754502180100000000000000)
      constant := (9387720347483636969057082975511929363671098307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26773710231574334981/10000000000000000000)
  centralHi := (267737102315743349811/100000000000000000000)
  directionLo := (68078534117061120339/25000000000000000000)
  directionHi := (272314136468244481357/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree031.table
  base := (-10331699501250361034430504958462994230133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-268228512731430778663066493476220000000000000)
      constant := (2445768675960951751022864704505574622703116507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree031.table
  base := (-5169077178765245906672995726353800999973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-544717716224143280936004217281710000000000000)
      constant := (4988861639383805042386508279034677862159865107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68078534117061120339/25000000000000000000)
  centralHi := (272314136468244481357/100000000000000000000)
  directionLo := (27681550152486138351/10000000000000000000)
  directionHi := (276815501524861383511/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree032.table
  base := (-5207326483092214267306447206509101415201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-137989517484295560521834200384170000000000000)
      constant := (1297460772235697403102886992688761407690192879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree032.table
  base := (-1302526626505132769685224011202504309179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-560464907758736083885631183473370000000000000)
      constant := (5293170146570405760571917290167762237718382644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27681550152486138351/10000000000000000000)
  centralHi := (276815501524861383511/100000000000000000000)
  directionLo := (281244830794230582433/100000000000000000000)
  directionHi := (140622415397115291217/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree033.table
  base := (-10461424271933629133784464500117595920377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-283729557205751463424270308060460000000000000)
      constant := (2748628153321155313197539331148008522714693783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree033.table
  base := (-10466208875522755116929318688620281470323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1152424198586657773670516299330060000000000000)
      constant := (11213531476540192541730556514547357561409380757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281244830794230582433/100000000000000000000)
  centralHi := (140622415397115291217/50000000000000000000)
  directionLo := (285605475809708954661/100000000000000000000)
  directionHi := (142802737904854477331/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree034.table
  base := (-10473067444211347176481361294265192466643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-291480079442911805804872215352580000000000000)
      constant := (2906880153572557554605089928760885410471720797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree034.table
  base := (-2095436194797773545535737833111935539073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1183918581655843379569770231713380000000000000)
      constant := (11859263537533261096203022992563062366962810035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285605475809708954661/100000000000000000000)
  centralHi := (142802737904854477331/50000000000000000000)
  directionLo := (1449502680029473961/500000000000000000)
  directionHi := (289900536005894792201/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree035.table
  base := (-10450462418190668489880896638295605319589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-299230601680072148185474122644700000000000000)
      constant := (3069670575259095517591354291109060510263535531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree035.table
  base := (-5226997969033879218777977637294952288341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-607706482362514492734512082048350000000000000)
      constant := (6261754354204026975767219745063932433729266019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1449502680029473961/500000000000000000)
  centralHi := (289900536005894792201/100000000000000000000)
  directionLo := (294132884493590683589/100000000000000000000)
  directionHi := (29413288449359068359/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree036.table
  base := (-1039434379402085470943024486963776012441/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-153490561958616245283038014968410000000000000)
      constant := (1618496799806493450370977675132879651027274195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree036.table
  base := (-5198688304122029726064660829070873270589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-623453673897107295684139048240010000000000000)
      constant := (6603121914316301503613097581146820149537057851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294132884493590683589/100000000000000000000)
  centralHi := (29413288449359068359/10000000000000000000)
  directionLo := (298305190542395381177/100000000000000000000)
  directionHi := (149152595271197690589/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree037.table
  base := (-5152662421102839208638703760515326021703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-157365823077196416473338968614470000000000000)
      constant := (1704422184459285660716849393045078102582090537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree037.table
  base := (-10307925893306201026278275718625864837607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1278401730863400197267532028863340000000000000)
      constant := (13907449580406418169481696353199748664738234113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298305190542395381177/100000000000000000000)
  centralHi := (149152595271197690589/50000000000000000000)
  directionLo := (75604984817698061759/25000000000000000000)
  directionHi := (302419939270792247037/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree038.table
  base := (-2545979385933172867591415362607158261539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-161241084195776587663639922260530000000000000)
      constant := (1792609413887223190703868451295197398820699162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree038.table
  base := (-407445866795122381911183728681350981493/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1309896113932585803166785961246660000000000000)
      constant := (14627109851059593814960187390688260830049569675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75604984817698061759/25000000000000000000)
  centralHi := (302419939270792247037/100000000000000000000)
  directionLo := (61295889791262358899/20000000000000000000)
  directionHi := (4788741389942371789/1562500000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree039.table
  base := (-5015274660021692110503835909501637289757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-165116345314356758853940875906590000000000000)
      constant := (1883056795287687017791700539512417531027834803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree039.table
  base := (-10032458380043074352605332398334798498043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1341390497001771409066039893629980000000000000)
      constant := (15365211201248334463897787556532114721324204237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61295889791262358899/20000000000000000000)
  centralHi := (4788741389942371789/1562500000000000000)
  directionLo := (310485886308185323713/100000000000000000000)
  directionHi := (155242943154092661857/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree040.table
  base := (-2461394249913812939677591479442350603747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-168991606432936930044241829552650000000000000)
      constant := (1975762915441333602678353472160674281735440026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree040.table
  base := (-9847210874987079272542240350989450615299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1372884880070957014965293826013300000000000000)
      constant := (16121742421390794814490217687269947012835204741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310485886308185323713/100000000000000000000)
  centralHi := (155242943154092661857/50000000000000000000)
  directionLo := (157220639994081437583/50000000000000000000)
  directionHi := (314441279988162875167/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree041.table
  base := (-1203662309736519530940201943327068725071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-172866867551517101234542783198710000000000000)
      constant := (2070726594533732789263115652976505154514850436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree041.table
  base := (-9630695961638942226828698593202047921091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1404379263140142620864547758396620000000000000)
      constant := (16896694161701167009737160800676973182560323269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157220639994081437583/50000000000000000000)
  centralHi := (314441279988162875167/100000000000000000000)
  directionLo := (12733901304760240341/4000000000000000000)
  directionHi := (159173766309503004263/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree042.table
  base := (-9381962450768165506595753722706586572287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-353484257340194544849687473689540000000000000)
      constant := (4335893695208641723896452692090881127760914673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree042.table
  base := (-9383157033448596876772695150160192710297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1435873646209328226763801690779940000000000000)
      constant := (17690058623609921725196647652438157265369373823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12733901304760240341/4000000000000000000)
  centralHi := (159173766309503004263/50000000000000000000)
  directionLo := (80551607870600552713/25000000000000000000)
  directionHi := (322206431482402210853/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree043.table
  base := (-1820755308224811690022725631566525822809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-361234779577354887230289380981660000000000000)
      constant := (4534845704725673831688144608009847744787649555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree043.table
  base := (-4552398551597264444546596707065204681501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-733684014639256916331527811581630000000000000)
      constant := (9250914651192311750810667968250943776800026459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80551607870600552713/25000000000000000000)
  centralHi := (322206431482402210853/100000000000000000000)
  directionLo := (163009829038496024159/50000000000000000000)
  directionHi := (326019658076992048319/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree044.table
  base := (-8794914082571130591267473461828054549109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-368985301814515229610891288273780000000000000)
      constant := (4738307844643026830141311363365419979916507611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree044.table
  base := (-2198946375740893036820844305674516869901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-749431206173849719281154777773290000000000000)
      constant := (9666000386227939047275110274764045609943004118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163009829038496024159/50000000000000000000)
  centralHi := (326019658076992048319/100000000000000000000)
  directionLo := (329788796681533228967/100000000000000000000)
  directionHi := (41223599585191653621/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree045.table
  base := (-8455519782933398339916652485547813294683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-376735824051675571991493195565900000000000000)
      constant := (4946278968730026685273456945015975770892815957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree045.table
  base := (-4228131736225466579300629044779496324339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-765178397708442522230781743964950000000000000)
      constant := (10090284254181305696142123772303220158271854101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329788796681533228967/100000000000000000000)
  centralHi := (41223599585191653621/12500000000000000000)
  directionLo := (33351534204691171667/10000000000000000000)
  directionHi := (333515342046911716671/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree046.table
  base := (-4042857226130885204796670095202393878073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-192243173144417957186047551429010000000000000)
      constant := (2579379060025130074582346497546081838091783767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree046.table
  base := (-1617269764006824865349282646244498541593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1561851178486070650360817420313220000000000000)
      constant := (21047528735406599519896478768142760111144093435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33351534204691171667/10000000000000000000)
  centralHi := (333515342046911716671/100000000000000000000)
  directionLo := (337200706322930727081/100000000000000000000)
  directionHi := (168600353161465363541/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree047.table
  base := (-3842799474962417865467310334424688987809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-196118434262998128376348505075070000000000000)
      constant := (2687872249848334314447721585248842038527564911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree047.table
  base := (-7686139810469094781987551159426073170619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1593345561555256256260071352696540000000000000)
      constant := (21932878305086797111303974530712469189540196621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337200706322930727081/100000000000000000000)
  centralHi := (168600353161465363541/50000000000000000000)
  directionLo := (85211556327728455587/25000000000000000000)
  directionHi := (340846225310913822349/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree048.table
  base := (-1451051495952257342956988805158455567267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-399987390763156599133298917442260000000000000)
      constant := (5597237440690645841879408581951539367258390465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree048.table
  base := (-1813929601882445715696388318912758008033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-812419972312220931079662642539930000000000000)
      constant := (11418307295600961704102054865665352641329229294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85211556327728455587/25000000000000000000)
  centralHi := (340846225310913822349/100000000000000000000)
  directionLo := (344453164120629158081/100000000000000000000)
  directionHi := (172226582060314579041/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree049.table
  base := (-6794760340974534121269517180328346617011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-407737913000316941513900824734380000000000000)
      constant := (5823236386192201571485637465447579166446655869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree049.table
  base := (-849394122327606741742423796540379432261/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-828167163846813734029289608731590000000000000)
      constant := (11879367701595982763821680273418678810443701196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344453164120629158081/100000000000000000000)
  centralHi := (172226582060314579041/50000000000000000000)
  directionLo := (8700568057486531951/2500000000000000000)
  directionHi := (348022722299461278041/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree050.table
  base := (-1260833244932899301198249891552102586909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-415488435237477283894502732026500000000000000)
      constant := (6053740871309133362835199176220078977045469055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree050.table
  base := (-6304500550634696065211479011255695945227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1687828710762813073957833149846500000000000000)
      constant := (24699238913858264463478469388175356246218981693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8700568057486531951/2500000000000000000)
  centralHi := (348022722299461278041/100000000000000000000)
  directionLo := (351556038492788228041/100000000000000000000)
  directionHi := (175778019246394114021/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree051.table
  base := (-2891762065521811244017286271691046644493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-211619478737318813137552319659310000000000000)
      constant := (3144375253955379205208162965444915219528970947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree051.table
  base := (-5783808691511634776966154150720802203589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1719323093831998679857087082229820000000000000)
      constant := (25658123599076444245711442598946714776594804851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351556038492788228041/100000000000000000000)
  centralHi := (175778019246394114021/50000000000000000000)
  directionLo := (17752709734344617387/5000000000000000000)
  directionHi := (355054194686892347741/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree052.table
  base := (-1308218742497176619489829890959331217147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-215494739855898984327853273305370000000000000)
      constant := (3264132485974971312851486645630342274857957226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree052.table
  base := (-5233117079607883001598698336832634280261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1750817476901184285756341014613140000000000000)
      constant := (26635388187512293455775402931091385565026157299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17752709734344617387/5000000000000000000)
  centralHi := (355054194686892347741/100000000000000000000)
  directionLo := (358518220079220674217/100000000000000000000)
  directionHi := (179259110039610337109/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree053.table
  base := (-4652252897231917754279793593217872002827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-438740001948958311036308453902860000000000000)
      constant := (6772283992879131495840029462682761235865607333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree053.table
  base := (-2326229406335589039628125097169348796291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-891155929985184945827797473498230000000000000)
      constant := (13815515809340438420777347957966916895218040069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358518220079220674217/100000000000000000000)
  centralHi := (179259110039610337109/50000000000000000000)
  directionLo := (361949094615233657427/100000000000000000000)
  directionHi := (90487273653808414357/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree054.table
  base := (-4041686429855517107079078823934162652207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-446490524186118653416910361194980000000000000)
      constant := (7020807344814516433109246335267977497631868353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree054.table
  base := (-2020930749814625986124731757273170038887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-906903121519777748777424439689890000000000000)
      constant := (14322526503982270471622462947673390358784021633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361949094615233657427/100000000000000000000)
  centralHi := (90487273653808414357/25000000000000000000)
  directionLo := (11417117257071546783/3125000000000000000)
  directionHi := (365347752226289497057/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree055.table
  base := (-680239875508535637446825544857643112749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-454241046423278995797512268487100000000000000)
      constant := (7273834839159597019022027568514913044519575855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree055.table
  base := (-340134817122754684756702638826916101211/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-922650313054370551727051405881550000000000000)
      constant := (14838725808717585524186804157106233906005491745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11417117257071546783/3125000000000000000)
  centralHi := (365347752226289497057/100000000000000000000)
  directionLo := (92178770949720670391/25000000000000000000)
  directionHi := (73743016759776536313/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree056.table
  base := (-2730811620015984524908989458217403876249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-461991568660439338178114175779220000000000000)
      constant := (7531366318447090669435943728996019943896231671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree056.table
  base := (-1365469019786654501956520563252483417399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-938397504588963354676678372073210000000000000)
      constant := (15364113415758819439141982515192107178823118641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92178770949720670391/25000000000000000000)
  centralHi := (73743016759776536313/20000000000000000000)
  directionLo := (372051939901987252203/100000000000000000000)
  directionHi := (93012984975496813051/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree057.table
  base := (-507634939017196749013152053226790332431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-234871045448799840279358041535670000000000000)
      constant := (3896700825598977626031301614902301187553628098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree057.table
  base := (-507661782914003271891275886988802946547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-954144696123556157626305338264870000000000000)
      constant := (15898689068345587337917307798117503529579375146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372051939901987252203/100000000000000000000)
  centralHi := (93012984975496813051/25000000000000000000)
  directionLo := (37535913329616316937/10000000000000000000)
  directionHi := (375359133296163169371/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree058.table
  base := (-1300397645398426517722715053912854625819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-477492613134760022939317990363460000000000000)
      constant := (8059940727629528129497991783170396278508887701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree058.table
  base := (-1300488817754374714962212128283629186861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1939783775316297921151864608913060000000000000)
      constant := (32884905104558678113959238061606104237223786699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37535913329616316937/10000000000000000000)
  centralHi := (375359133296163169371/100000000000000000000)
  directionLo := (94659360311349309667/25000000000000000000)
  directionHi := (378637441245397238669/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree059.table
  base := (-540396860947228686285820428252296072359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-485243135371920365319919897655580000000000000)
      constant := (8330983456072533140693290259842573562810844361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree059.table
  base := (-540474252170704566820226415517675703003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-1971278158385483527051118541296380000000000000)
      constant := (33990807377725148856137015570719158152800080877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94659360311349309667/25000000000000000000)
  centralHi := (378637441245397238669/100000000000000000000)
  directionLo := (7637752153006184109/2000000000000000000)
  directionHi := (381887607650309205451/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree060.table
  base := (249452933467314734414182884423699114719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-492993657609080707700521804947700000000000000)
      constant := (8606529759979871933387091185113520120687689199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree060.table
  base := (249387259160476934288594650362349758677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2002772541454669132950372473679700000000000000)
      constant := (35115084658019138933508310374878260048617769757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7637752153006184109/2000000000000000000)
  centralHi := (381887607650309205451/100000000000000000000)
  directionLo := (3851103450193091839/1000000000000000000)
  directionHi := (385110345019309183901/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree061.table
  base := (33410739621663000946458384461604372937/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-250372089923120525040561856119910000000000000)
      constant := (4443289787714727406448041352916205891808543632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree061.table
  base := (1069087952056324830697576397315195263133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2034266924523854738849626406063020000000000000)
      constant := (36257736696668465810784524550916536171426044453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3851103450193091839/1000000000000000000)
  centralHi := (385110345019309183901/100000000000000000000)
  directionLo := (388306336292502718559/100000000000000000000)
  directionHi := (2426914601828141991/625000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree062.table
  base := (383733720610750049472747520417549858663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-508494702083401392461725619531940000000000000)
      constant := (9171132849039470840859885100161377062152348115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree062.table
  base := (383724269668401766588891003690319065353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2065761307593040344748880338446340000000000000)
      constant := (37418763286105929750660997704197447565864877365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388306336292502718559/100000000000000000000)
  centralHi := (2426914601828141991/625000000000000000)
  directionLo := (391476236531569141781/100000000000000000000)
  directionHi := (195738118265784570891/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree063.table
  base := (4476835377001740223481811596185212511/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-516245224320561734842327526824060000000000000)
      constant := (9460189536227974882860675871246604417687269375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree063.table
  base := (2797982042538618052407222789644214636551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2097255690662225950648134270829660000000000000)
      constant := (38598164253134580969355392085232230281169730591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391476236531569141781/100000000000000000000)
  centralHi := (195738118265784570891/50000000000000000000)
  directionLo := (197310337243728772309/50000000000000000000)
  directionHi := (394620674487457544619/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree064.table
  base := (3707199489809088099297873693152670767813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-523995746557722077222929434116180000000000000)
      constant := (9753749599759921108103573343023622305151846773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree064.table
  base := (741433104788457648450321708530608401453/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2128750073731411556547388203212980000000000000)
      constant := (39795939453226956952534890811519306118954777865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197310337243728772309/50000000000000000000)
  centralHi := (394620674487457544619/100000000000000000000)
  directionLo := (198870127028263587451/50000000000000000000)
  directionHi := (397740254056527174903/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree065.table
  base := (4646196814186423575762417740824693941323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-531746268794882419603531341408300000000000000)
      constant := (10051813008534165782100832018901072400709219483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree065.table
  base := (4646168028222370141084733100644625378941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2160244456800597162446642135596300000000000000)
      constant := (41012088765770139367215204641353754441766648581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198870127028263587451/50000000000000000000)
  centralHi := (397740254056527174903/100000000000000000000)
  directionLo := (400835555634683732551/100000000000000000000)
  directionHi := (50104444454335466569/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree066.table
  base := (561501080388120005419835703175066901711/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-269748395516021380992066624350210000000000000)
      constant := (5177189868285402013680327740594628524642264155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree066.table
  base := (1122997282728158633076395165867266658591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2191738839869782768345896067979620000000000000)
      constant := (42246612090099698693829621204992525455039571155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (400835555634683732551/100000000000000000000)
  centralHi := (50104444454335466569/12500000000000000000)
  directionLo := (40390713737811132389/10000000000000000000)
  directionHi := (403907137378111323891/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree067.table
  base := (3306819359412368126792171422255686193091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-273623656634601552182367577996270000000000000)
      constant := (5330724881082875909728036813332907290335473811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree067.table
  base := (1653404514451862159454121640436928291883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1111616611469484187122575000181470000000000000)
      constant := (21749754671095816730123955448117699238800446406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40390713737811132389/10000000000000000000)
  centralHi := (403907137378111323891/100000000000000000000)
  directionLo := (406955536378355896803/100000000000000000000)
  directionHi := (101738884094588974201/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree068.table
  base := (7642078269652130462273806279295549385551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-554997835506363446745337063284660000000000000)
      constant := (10973023067184949771929133983075340046682949471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree068.table
  base := (3821030385782122555139740845787787309621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1127363803004076990072201966373130000000000000)
      constant := (22385390225951564629190610089776406493187566461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406955536378355896803/100000000000000000000)
  centralHi := (101738884094588974201/25000000000000000000)
  directionLo := (409981269758766181703/100000000000000000000)
  directionHi := (51247658719845772713/12500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree069.table
  base := (1740065508662651495689307481434215923327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-562748357743523789125938970576780000000000000)
      constant := (11289099636475127843056218667570762121643365835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree069.table
  base := (8700312727155848548740474440514068559997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2286221989077339586043657865129580000000000000)
      constant := (46060425360671077430445178228081071270730863877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409981269758766181703/100000000000000000000)
  centralHi := (51247658719845772713/12500000000000000000)
  directionLo := (206492417849315390813/50000000000000000000)
  directionHi := (412984835698630781627/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree070.table
  base := (9788384940968707914603284322016179597153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-570498879980684131506540877868900000000000000)
      constant := (11609679457371879071078946105803690158589048913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree070.table
  base := (1223546549789584167193749468106595448581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1158858186073262595971455898756450000000000000)
      constant := (23684222009796201173864380201774913699071935284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206492417849315390813/50000000000000000000)
  centralHi := (412984835698630781627/100000000000000000000)
  directionLo := (207983357195377484851/50000000000000000000)
  directionHi := (415966714390754969703/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree071.table
  base := (5453124563070813269139217794268582758003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-289124701108922236943571392580510000000000000)
      constant := (5967381259644485142850478094797581444026141763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree071.table
  base := (5453119255148500531994577017830692588847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1174605377607855398921082864948110000000000000)
      constant := (24347418193911424141285020350599493221239246727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207983357195377484851/50000000000000000000)
  centralHi := (415966714390754969703/100000000000000000000)
  directionLo := (52365921117211151727/12500000000000000000)
  directionHi := (418927368937689213817/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree072.table
  base := (12053918981431543692197610627494295405501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-585999924455004816267744692453140000000000000)
      constant := (12264348813375472366766978550377022313906973421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree072.table
  base := (12053909998179155123227591353309269511103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2380705138284896403741419662279540000000000000)
      constant := (50039602431241387958873649621644022304405251223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52365921117211151727/12500000000000000000)
  centralHi := (418927368937689213817/100000000000000000000)
  directionLo := (8437344923826917473/2000000000000000000)
  directionHi := (421867246191345873651/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree073.table
  base := (13231393572376076162258733039567186211909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-593750446692165158648346599745260000000000000)
      constant := (12598438332229508776838110640990251681984531189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree073.table
  base := (13231385972108278541354701098017211603327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2412199521354082009640673594662860000000000000)
      constant := (51402742121336181904338517418821409476982200407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8437344923826917473/2000000000000000000)
  centralHi := (421867246191345873651/100000000000000000000)
  directionLo := (42478677754031431893/10000000000000000000)
  directionHi := (424786777540314318931/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree074.table
  base := (14438672117279944192415836617186698973389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-601500968929325501028948507037380000000000000)
      constant := (12937031069659271204966712363104695842568214269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree074.table
  base := (14438665688290481597830574859797601150257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2443693904423267615539927527046180000000000000)
      constant := (52784255434275330098428824887366734938455384537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42478677754031431893/10000000000000000000)
  centralHi := (424786777540314318931/100000000000000000000)
  directionLo := (106921594912200542061/25000000000000000000)
  directionHi := (85537275929760433649/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree075.table
  base := (244933655656652227674036021563637435523/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-304625745583242921704775207164750000000000000)
      constant := (6640063510241747842236124853770278308056885856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree075.table
  base := (48986714140004618245134077162689444777/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1237594143746226610719590729714750000000000000)
      constant := (27092071175065878239432577734181657200015977120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106921594912200542061/25000000000000000000)
  centralHi := (85537275929760433649/20000000000000000000)
  directionLo := (430566455150786447601/100000000000000000000)
  directionHi := (215283227575393223801/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree076.table
  base := (8471319279521843997443899786316449294517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-308501006701823092895076160810810000000000000)
      constant := (6813863090182440980903697742546892594861869157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree076.table
  base := (16942633961407595000916258459991847529241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2506682670561638827338435391812820000000000000)
      constant := (55602402852236653952691942040779558786684410881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430566455150786447601/100000000000000000000)
  centralHi := (215283227575393223801/50000000000000000000)
  directionLo := (1354460604070777657/312500000000000000)
  directionHi := (433427393302648850241/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree077.table
  base := (9119662724876730957835934768456679121007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-312376267820403264085377114456870000000000000)
      constant := (6989914272835507666876750751011865355317496447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree077.table
  base := (18239321562733471806402026244230916689269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2538177053630824433237689324196140000000000000)
      constant := (57039036926640160569173596294189242801640868029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1354460604070777657/312500000000000000)
  centralHi := (433427393302648850241/100000000000000000000)
  directionLo := (218134785298645060787/50000000000000000000)
  directionHi := (17450782823891604863/4000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree078.table
  base := (978290712495235940692052073038640419941/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-316251528938983435275678068102930000000000000)
      constant := (7168217056679124406724712138132210707663526610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree078.table
  base := (9782905482110601770551004751135429447481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1284835718350005019568471628289730000000000000)
      constant := (29247022280830738251687655074545950294926738721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218134785298645060787/50000000000000000000)
  centralHi := (17450782823891604863/4000000000000000000)
  directionLo := (439093351342466543309/100000000000000000000)
  directionHi := (43909335134246654331/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree079.table
  base := (5230526159334385447244043712678494559923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-320126790057563606465979021748990000000000000)
      constant := (7348771440437376849563471897983432710818300166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree079.table
  base := (20922101860417824641264612906601745148637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2601165819769195645036197188962780000000000000)
      constant := (59967425747513583285668918739598786516307478117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439093351342466543309/100000000000000000000)
  centralHi := (43909335134246654331/10000000000000000000)
  directionLo := (220949544102931801737/50000000000000000000)
  directionHi := (17675963528234544139/4000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree080.table
  base := (5577049085440798911582432776626254082791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-324002051176143777656279975395050000000000000)
      constant := (7531577423039786459654232403939313117179575022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree080.table
  base := (22308193995204855955932063110341856614057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2632660202838381250935451121346100000000000000)
      constant := (61459180475990188725578584049902463427771000337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220949544102931801737/50000000000000000000)
  centralHi := (17675963528234544139/4000000000000000000)
  directionLo := (444687122729215622227/100000000000000000000)
  directionHi := (111171780682303905557/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree081.table
  base := (474481782724630723298287518861636302349/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-327877312294723948846580929041110000000000000)
      constant := (7716635003587517190809773318563855528772660725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree081.table
  base := (59310217884119335741818582029716826541/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1332077292953783428417352526864710000000000000)
      constant := (31484654370102287241992760476166111367840036200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444687122729215622227/100000000000000000000)
  centralHi := (111171780682303905557/25000000000000000000)
  directionLo := (89491557162718614353/20000000000000000000)
  directionHi := (223728892906796535883/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree082.table
  base := (12584891415003270036014535709569435902053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-331752573413304120036881882687170000000000000)
      constant := (7903944181325159022858562181090519501780161813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree082.table
  base := (12584890577598198879525641040252273253929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1347824484488376231366979493056370000000000000)
      constant := (32248905267185868013702229396033743087329139089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89491557162718614353/20000000000000000000)
  centralHi := (223728892906796535883/50000000000000000000)
  directionLo := (225105699088904782217/50000000000000000000)
  directionHi := (90042279635561912887/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree083.table
  base := (5329055452523484846247431114546512935909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-671255669063768582454365672666460000000000000)
      constant := (16187009911234334838377483183638054644826675945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree083.table
  base := (5329055169602577314437919757837878420877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2727143352045938068633212918496060000000000000)
      constant := (66044685853626633286821949906546857312416599785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225105699088904782217/50000000000000000000)
  centralHi := (90042279635561912887/20000000000000000000)
  directionLo := (22647413539587310077/5000000000000000000)
  directionHi := (452948270791746201541/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree084.table
  base := (703764307472280701166053199707365573339/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-339503095650464462417483789979290000000000000)
      constant := (8285317325928189869360263460853520854128364380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree084.table
  base := (14075285552119503798610702475617291968639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1379318867557561837266233425439690000000000000)
      constant := (33804967346936280947936913620049133651967162199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22647413539587310077/5000000000000000000)
  centralHi := (452948270791746201541/100000000000000000000)
  directionLo := (113917176321562648801/25000000000000000000)
  directionHi := (91133741057250119041/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree085.table
  base := (14842833912402397575743619460397125299577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-343378356769044633607784743625350000000000000)
      constant := (8479381291806637662582587680828805629497949417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree085.table
  base := (29685666816048128541074171172382741523919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2790132118184309280431720783262700000000000000)
      constant := (69193557051654648729257753878400315421167888679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113917176321562648801/25000000000000000000)
  centralHi := (91133741057250119041/20000000000000000000)
  directionLo := (229186497170569997071/50000000000000000000)
  directionHi := (458372994341139994143/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree086.table
  base := (15625281872010428419724125535315858272067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-347253617887624804798085697271410000000000000)
      constant := (8675696852870967046144317109919816913373042707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree086.table
  base := (1562528144617551965961877072856117368087/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1410813250626747443165487357823010000000000000)
      constant := (35397776462027152203327966752500408565908755670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229186497170569997071/50000000000000000000)
  centralHi := (458372994341139994143/100000000000000000000)
  directionLo := (461061422052721315139/100000000000000000000)
  directionHi := (23053071102636065757/5000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree087.table
  base := (16422629987497632554200443647203553611901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-351128879006204975988386650917470000000000000)
      constant := (8874264008798222421883038548500119348159867821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree087.table
  base := (6569051851209479345273119944216362815587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2853120884322680492230228648029340000000000000)
      constant := (72415922308601156831425877622640422404871115335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461061422052721315139/100000000000000000000)
  centralHi := (23053071102636065757/5000000000000000000)
  directionLo := (463734264282134395987/100000000000000000000)
  directionHi := (115933566070533598997/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree088.table
  base := (34469756448561077839489705712580536625983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-710008280249570294357375209127060000000000000)
      constant := (18150165518628936231074050038011590430614411343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree088.table
  base := (34469755841732266919459399630966963873369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2884615267391866098129482580412660000000000000)
      constant := (74054665203199566518304056991854052489466616129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463734264282134395987/100000000000000000000)
  centralHi := (115933566070533598997/25000000000000000000)
  directionLo := (466391788985727454551/100000000000000000000)
  directionHi := (58298973623215931819/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree089.table
  base := (18062026552955386068738341274088459959549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445000000000000000000000000000000000000000
      center := (1617)
      previous := (0)
      next := (1320)
      square := (39543480801838481533683200470000000000000)
      linear := (-4032352822959160880550433238310000000000000)
      constant := (104248911282997718344715576722113872936399861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree089.table
  base := (36124052593782292257244422443827477804397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2916109650461051704028736512795980000000000000)
      constant := (75711781606067305465106394757598836216330684277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466391788985727454551/100000000000000000000)
  centralHi := (58298973623215931819/12500000000000000000)
  directionLo := (469034256528584680471/100000000000000000000)
  directionHi := (58629282066073085059/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree090.table
  base := (1890407494845543156484752161152438364147/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-362754662361945489559289511855650000000000000)
      constant := (9483475043216655206472825715570384642824083870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree090.table
  base := (37808149464758530274262226231296733148789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2947604033530237309927990445179300000000000000)
      constant := (77387271515684382516297136982047978626820348349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469034256528584680471/100000000000000000000)
  centralHi := (58629282066073085059/12500000000000000000)
  directionLo := (471661919982244312749/100000000000000000000)
  directionHi := (1886647679928977251/400000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree091.table
  base := (494025584733675742742663928248931226563/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-366629923480525660749590465501710000000000000)
      constant := (9691048576234267029339687388105771369824220920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree091.table
  base := (39522046414073456285026269767882568806561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-2979098416599422915827244377562620000000000000)
      constant := (79081134930750332793428609397795485387131021001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471661919982244312749/100000000000000000000)
  centralHi := (1886647679928977251/400000000000000000)
  directionLo := (14821094543986586347/3125000000000000000)
  directionHi := (94855005081514152621/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree092.table
  base := (41265743714483147599034265365186180607221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-741010369198211663879782838295540000000000000)
      constant := (19801747406187952495158969783193079736589797541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree092.table
  base := (10316435851719583005884843650430396690539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1505296399834304260863249154972970000000000000)
      constant := (40396685925074283936859998205032600680723120198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14821094543986586347/3125000000000000000)
  centralHi := (94855005081514152621/20000000000000000000)
  directionLo := (476873812123675699807/100000000000000000000)
  directionHi := (14902306628864865619/3125000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree093.table
  base := (2151962033630418142467275955522585895647/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-374380445717686003130192372793830000000000000)
      constant := (10112950423670354757625725228937464028794198870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree093.table
  base := (43039240413134408341267499109398989585969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-3042087182737794127625752242329260000000000000)
      constant := (82523982272916616195703118791201293025324032729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476873812123675699807/100000000000000000000)
  centralHi := (14902306628864865619/3125000000000000000)
  directionLo := (239729256481859971593/50000000000000000000)
  directionHi := (479458512963719943187/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree094.table
  base := (44842537625686317875473059024022248550019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-756511413672532348640986652879780000000000000)
      constant := (20654557475709901308194121299984840230764700499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree094.table
  base := (44842537406837490120952659758249494650591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-3073581565806979733525006174712580000000000000)
      constant := (84272966198221277343625913490833632058099586231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239729256481859971593/50000000000000000000)
  centralHi := (479458512963719943187/100000000000000000000)
  directionLo := (120507338629592508311/25000000000000000000)
  directionHi := (96405870903674006649/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree095.table
  base := (23337817274966917310720498922126210794471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-382130967954846345510794280085950000000000000)
      constant := (10543858645553570660302798653261661715703004791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree095.table
  base := (5834454295671305779080136748326279665539/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1552537974438082669712130053547950000000000000)
      constant := (43020161812668937909476766001361989307054140396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120507338629592508311/25000000000000000000)
  centralHi := (96405870903674006649/20000000000000000000)
  directionLo := (242293278683814977153/50000000000000000000)
  directionHi := (484586557367629954307/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree096.table
  base := (24269265712297212320461212470752009424833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-386006229073426516701095233732010000000000000)
      constant := (10762690146684008703751261509196506666654102193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree096.table
  base := (24269265634481231696025793477031875205247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1568285165972675472661757019739610000000000000)
      constant := (43913027276816467496622159961085258313451319127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242293278683814977153/50000000000000000000)
  centralHi := (484586557367629954307/100000000000000000000)
  directionLo := (3805705752357182261/781250000000000000)
  directionHi := (487130336301719329409/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree097.table
  base := (5043122823145883850409447251192367177643/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-389881490192006687891396187378070000000000000)
      constant := (10983773241174147052075635749859793702070551015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree097.table
  base := (1008624562004747186571557302330933347179/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1584032357507268275611383985931270000000000000)
      constant := (44815079491274852305182890819273955884424058475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3805705752357182261/781250000000000000)
  centralHi := (487130336301719329409/100000000000000000000)
  directionLo := (244830450265812028487/50000000000000000000)
  directionHi := (19586436021264962279/4000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree098.table
  base := (26176862477232086128108225675349863286201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-393756751310586859081697141024130000000000000)
      constant := (11207107928960368574163170875655866267089998121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree098.table
  base := (26176862421918101895573590988930155659309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1599779549041861078561010952122930000000000000)
      constant := (45726318455798034593071647640685731117479919669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244830450265812028487/50000000000000000000)
  centralHi := (19586436021264962279/4000000000000000000)
  directionLo := (246089226944951759629/50000000000000000000)
  directionHi := (492178453889903519259/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree099.table
  base := (27153010789679289973863542986879450365639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-397632012429167030271998094670190000000000000)
      constant := (11432694209986228834130629455030052126346226519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree099.table
  base := (54306021486101942417818811423939438236391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-3231053481152907763021275836629180000000000000)
      constant := (93293488340334443041765918045220403540532204031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246089226944951759629/50000000000000000000)
  centralHi := (492178453889903519259/100000000000000000000)
  directionLo := (494683195022299843451/100000000000000000000)
  directionHi := (123670798755574960863/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree100.table
  base := (56288118093420779307366234990513941537849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-803014547095494402924598096632500000000000000)
      constant := (23321064168402690387085371396009860930921301929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree100.table
  base := (28144059007407879555153379741633400905091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1631273932111046684460264884506250000000000000)
      constant := (47576356634186661545314234198626675798400020731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494683195022299843451/100000000000000000000)
  centralHi := (123670798755574960863/25000000000000000000)
  directionLo := (124293829392664742157/25000000000000000000)
  directionHi := (497175317570658968629/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree101.table
  base := (7287501810653165323339368353841553373157/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-405382534666327372652600001962310000000000000)
      constant := (11890621551560467166591726346886595777075106388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree101.table
  base := (14575003604744153657876999393592146362053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1647021123645639487409891850697910000000000000)
      constant := (48515155847680112517267464099345651923173080346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124293829392664742157/25000000000000000000)
  centralHi := (497175317570658968629/100000000000000000000)
  directionLo := (499655010347640217221/100000000000000000000)
  directionHi := (249827505173820108611/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree102.table
  base := (30170855372223047392885801780993709422399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-409257795784907543842900955608370000000000000)
      constant := (12122962612022698174820244993853671172334822479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree102.table
  base := (1206834213772336377050576818648463968013/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1662768315180232290359518816889570000000000000)
      constant := (49463141810487887057032707447992305849977613325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499655010347640217221/100000000000000000000)
  centralHi := (249827505173820108611/50000000000000000000)
  directionLo := (251061228751830231951/50000000000000000000)
  directionHi := (502122457503660463903/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree103.table
  base := (62413206861691745561243511254069425236037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-826266113806975430066403818508860000000000000)
      constant := (24715110531101687550387261849191123917294649077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree103.table
  base := (1950412712957739945798880497698309558609/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1678515506714825093309145783081230000000000000)
      constant := (50420314522464379750268172421639844585078255504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251061228751830231951/50000000000000000000)
  centralHi := (502122457503660463903/100000000000000000000)
  directionLo := (504577838686490634181/100000000000000000000)
  directionHi := (252288919343245317091/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree104.table
  base := (32257251414183899883523361380689772563799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-417008318022067886223502862900490000000000000)
      constant := (12594399512110865548895818666442123688477851879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree104.table
  base := (64514502788730248126695073356432799618031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-3388525396498835792517545498545780000000000000)
      constant := (102773347966951993065407811630088823332561331271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504577838686490634181/100000000000000000000)
  centralHi := (252288919343245317091/50000000000000000000)
  directionLo := (101404265838779192937/20000000000000000000)
  directionHi := (253510664596947982343/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree105.table
  base := (66645598636561058711634124299512196980637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-841767158281296114827607633093100000000000000)
      constant := (25666990703342846545017871750500436112283625677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree105.table
  base := (66645598603167042490908022146978928784611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-3420019779568021398416799430929100000000000000)
      constant := (104724440386798839661515637348035351857187721051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101404265838779192937/20000000000000000000)
  centralHi := (253510664596947982343/50000000000000000000)
  directionLo := (254726550059843524553/50000000000000000000)
  directionHi := (509453100119687049107/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree106.table
  base := (13761298855788525633260405596466180794533/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-849517680518456457208209540385220000000000000)
      constant := (26149685568406981720880403190293603090367479465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree106.table
  base := (17201623562702810658799335929144838258269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1725757081318603502158026681656210000000000000)
      constant := (53346953152120154035077998524846239525266394058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254726550059843524553/50000000000000000000)
  centralHi := (509453100119687049107/100000000000000000000)
  directionLo := (127968329623381506313/25000000000000000000)
  directionHi := (511873318493526025253/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree107.table
  base := (70997189748686513570865383218992131087727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-857268202755616799588811447677340000000000000)
      constant := (26636883619360067922468005866533676670345885567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree107.table
  base := (35498594862495258804347378743693059468603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1741504272853196305107653647847870000000000000)
      constant := (54340872859531305067666060078532689318433508723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127968329623381506313/25000000000000000000)
  centralHi := (511873318493526025253/100000000000000000000)
  directionLo := (514282147414811190371/100000000000000000000)
  directionHi := (128570536853702797593/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree108.table
  base := (36608842519700613750191685820544246592711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-432509362496388570984706677484730000000000000)
      constant := (13564292428075739088943861778462250977260863831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree108.table
  base := (7321768501944304881342546924554749022771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1757251464387789108057280614039530000000000000)
      constant := (55343979315532555463673148144374013567193028055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514282147414811190371/100000000000000000000)
  centralHi := (128570536853702797593/25000000000000000000)
  directionLo := (258339873090471868561/50000000000000000000)
  directionHi := (516679746180943737123/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree109.table
  base := (754679801450722757604912688002575984837/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-436384623614968742175007631130790000000000000)
      constant := (13812394639366785839312996639555300218794693850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree109.table
  base := (9433497516032968672455911419874336525473/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1772998655922381911006907580231190000000000000)
      constant := (56356272520029302778902558005410654466450721572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258339873090471868561/50000000000000000000)
  centralHi := (516679746180943737123/100000000000000000000)
  directionLo := (12976656760256551637/2500000000000000000)
  directionHi := (519066270410262065481/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree110.table
  base := (77748075060013740228663994770260496768523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-880519769467097826730617169553700000000000000)
      constant := (28125496887061310267234293874996233394903470683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree110.table
  base := (38874037522929500906328293156672482180227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1788745847456974713956534546422850000000000000)
      constant := (57377752472931934464280390036843443001536653307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12976656760256551637/2500000000000000000)
  centralHi := (519066270410262065481/100000000000000000000)
  directionLo := (260720936079956070449/50000000000000000000)
  directionHi := (521441872159912140899/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree111.table
  base := (20014492444706867560284302470317890047637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-444135145852129084555609538422910000000000000)
      constant := (14315353840545967596152474005028356014134665354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree111.table
  base := (80057969766908514927326592952563933942811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-3608986077983135033812323025229020000000000000)
      constant := (116816838348310433589750641923144261007461607251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260720936079956070449/50000000000000000000)
  centralHi := (521441872159912140899/100000000000000000000)
  directionLo := (52380670003890653957/10000000000000000000)
  directionHi := (523806700038906539571/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree112.table
  base := (2059941607409215988243955459771878993617/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-448010406970709255745910492068970000000000000)
      constant := (14570210830392347142483959090658181070168805140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree112.table
  base := (82397664286333132605583817876667526908261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-3640480461052320639711576957612340000000000000)
      constant := (118896545247235558300195508757164544229667590701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52380670003890653957/10000000000000000000)
  centralHi := (523806700038906539571/100000000000000000000)
  directionLo := (526160899316610059491/100000000000000000000)
  directionHi := (131540224829152514873/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree113.table
  base := (10595894825964578805675718033984371070129/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-451885668089289426936211445715030000000000000)
      constant := (14827319413050305666412257380681880812985967236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree113.table
  base := (42383579299633810022487994829194039069181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1835987422060753122805415444997830000000000000)
      constant := (60497312821241678035795003673473326205815628421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526160899316610059491/100000000000000000000)
  centralHi := (131540224829152514873/25000000000000000000)
  directionLo := (528504612026876000217/100000000000000000000)
  directionHi := (264252306013438000109/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree114.table
  base := (87166452708150378148226116947987887509607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-911521858415739196253024798722180000000000000)
      constant := (30173359177002290781278256825564172056963597047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree114.table
  base := (43583226350518807140600137921281582814753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1851734613595345925755042411189490000000000000)
      constant := (61555539766952027820097455318897363194967500873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528504612026876000217/100000000000000000000)
  centralHi := (264252306013438000109/50000000000000000000)
  directionLo := (530837977068044350843/100000000000000000000)
  directionHi := (132709494267011087711/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree115.table
  base := (89595546593127450179366605097108686722133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-919272380652899538633626706014300000000000000)
      constant := (30696582713453752022822571889115197907526015493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree115.table
  base := (22398886646785015043801233469737197392683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1867481805129938728704669377381150000000000000)
      constant := (62622953460676687308149930873328199083317912006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530837977068044350843/100000000000000000000)
  centralHi := (132709494267011087711/25000000000000000000)
  directionLo := (533161130299001106829/100000000000000000000)
  directionHi := (53316113029900110683/10000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree116.table
  base := (92054440258266256012199189423928931269341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-927022902890059881014228613306420000000000000)
      constant := (31224309435420288478896039411178701064584450061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree116.table
  base := (46027220126613282593150971517512169173599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1883228996664531531654296343572810000000000000)
      constant := (63699553902345993077254337900620487412491285559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533161130299001106829/100000000000000000000)
  centralHi := (53316113029900110683/10000000000000000000)
  directionLo := (535474204631486699621/100000000000000000000)
  directionHi := (267737102315743349811/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree117.table
  base := (94543133699330880701959146194002352566463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-934773425127220223394830520598540000000000000)
      constant := (31756539342868347467221178015054132634678953423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree117.table
  base := (23635783423772299950422385389847232744167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1898976188199124334603923309764470000000000000)
      constant := (64785341091892531992650835776635910368711709694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535474204631486699621/100000000000000000000)
  centralHi := (267737102315743349811/50000000000000000000)
  directionLo := (21511093204753240453/4000000000000000000)
  directionHi := (268888665059415505663/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree118.table
  base := (97061626912218119857762313536896352317931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-942523947364380565775432427890660000000000000)
      constant := (32293272435765427505817794254565796006710331451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree118.table
  base := (97061626908648348541896505298702508462829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-3829446759467434275107100551912260000000000000)
      constant := (131760630058501893149101111509651767073657503989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21511093204753240453/4000000000000000000)
  centralHi := (268888665059415505663/50000000000000000000)
  directionLo := (270035317020641303727/50000000000000000000)
  directionHi := (108014126808256521491/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree119.table
  base := (19921983978589272512086836416693705212367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-950274469601540908156034335182780000000000000)
      constant := (32834508714079990254595106841000714194935795035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree119.table
  base := (9960991988994228158161496995388251982727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1930470571268309940503177242147790000000000000)
      constant := (66984475714357767930287153195186954908892779035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270035317020641303727/50000000000000000000)
  centralHi := (108014126808256521491/20000000000000000000)
  directionLo := (271177120494045302823/50000000000000000000)
  directionHi := (542354240988090605647/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree120.table
  base := (102188012637646026806191966651317836388799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-958024991838701250536636242474900000000000000)
      constant := (33380248177781384754501152332929088582035676879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree120.table
  base := (102188012635118171360389966246700859764219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-3892435525605805486905608416678900000000000000)
      constant := (136195646294302543671856718524794542247705340979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271177120494045302823/50000000000000000000)
  centralHi := (542354240988090605647/100000000000000000000)
  directionLo := (68078534117061120339/12500000000000000000)
  directionHi := (544628272936488962713/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree121.table
  base := (52397952571275650229496770534066881000741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-482887757037930796458619074883510000000000000)
      constant := (16965245413419891003803170524470023764406869461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree121.table
  base := (104795905140424323896161052611895162214451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-3923929908674991092804862349062220000000000000)
      constant := (138440714655142708556069149304721092892513224491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68078534117061120339/12500000000000000000)
  centralHi := (544628272936488962713/100000000000000000000)
  directionLo := (546892849327724865491/100000000000000000000)
  directionHi := (136723212331931216373/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree122.table
  base := (107433597403992981120371732686852440664773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-973526036313021935297840057059140000000000000)
      constant := (34485236661226118261712414514496198182505666933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree122.table
  base := (107433597402203432348485136044269672944483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-3955424291744176698704116281445540000000000000)
      constant := (140704156511118846744736961587174084590814179803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546892849327724865491/100000000000000000000)
  centralHi := (136723212331931216373/25000000000000000000)
  directionLo := (549148087140265314997/100000000000000000000)
  directionHi := (274574043570132657499/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree123.table
  base := (110101089418392242091437360029225815641531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-981276558550182277678441964351260000000000000)
      constant := (35044485680912045630537471523108337685696567051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree123.table
  base := (13762636177110836493964330936309409449337/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-1993459337406681152301685106914430000000000000)
      constant := (71492985931058305082182020806057579152664827268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549148087140265314997/100000000000000000000)
  centralHi := (274574043570132657499/50000000000000000000)
  directionLo := (551394100960308863361/100000000000000000000)
  directionHi := (275697050480154431681/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree124.table
  base := (112798381182255179806663834126517732189489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-989027080787342620059043871643380000000000000)
      constant := (35608237885869888903938975963555106956672942369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree124.table
  base := (4511935247239545671574033498981814323111/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-4018413057882547910502624146212180000000000000)
      constant := (145286160708024321161724852947584867818169988775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551394100960308863361/100000000000000000000)
  centralHi := (275697050480154431681/50000000000000000000)
  directionLo := (553631003049722767021/100000000000000000000)
  directionHi := (276815501524861383511/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree125.table
  base := (11552547269216802168075586574860762873969/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-498388801512251481219822889467750000000000000)
      constant := (18088246638036303794634401924922360513623542245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree125.table
  base := (115525472691102620874964332623291205022607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-4049907440951733516401878078595500000000000000)
      constant := (147604723048732826912153212041332873500129350887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553631003049722767021/100000000000000000000)
  centralHi := (276815501524861383511/50000000000000000000)
  directionLo := (69482362926439940973/12500000000000000000)
  directionHi := (111171780682303905557/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree126.table
  base := (118282363944792892994513317841617296783961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-1004528125261663304820247686227620000000000000)
      constant := (36749251851493762380876170896373410607825755081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree126.table
  base := (14785295492987093045574373528412609828483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-2040700912010459561150566005489410000000000000)
      constant := (74970829442067685246681895948362453726057695212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69482362926439940973/12500000000000000000)
  centralHi := (111171780682303905557/20000000000000000000)
  directionLo := (17439934682905652447/3125000000000000000)
  directionHi := (111615581970596175661/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree127.table
  base := (121069054936864057892779506326915317770297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-1012278647498823647200849593519740000000000000)
      constant := (37326513612107485385052381008554336232058522537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree127.table
  base := (121069054936110321052753570871270819561933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-4112896207090104728200385943362140000000000000)
      constant := (152296968214127476098441511985901228329583895253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17439934682905652447/3125000000000000000)
  centralHi := (111615581970596175661/20000000000000000000)
  directionLo := (140072032011632926223/25000000000000000000)
  directionHi := (560288128046531704893/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree128.table
  base := (61942772832592281655676199153425727936099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (143913)
      previous := (0)
      next := (117480)
      square := (3519369791363624856497804841830000000000000)
      linear := (-510014584867991994790725750405930000000000000)
      constant := (18954139278944226768287944941902605190981840179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree128.table
  base := (123885545664550646101490630363527957772557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1169586)
      previous := (0)
      next := (945120)
      square := (28472194794869815434174009578860000000000000)
      linear := (-4144390590159290334099639875745460000000000000)
      constant := (154670651038606846271673633975270439294990498837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell161.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140072032011632926223/25000000000000000000)
  centralHi := (560288128046531704893/100000000000000000000)
  directionLo := (281244830794230582433/50000000000000000000)
  directionHi := (562489661588461164867/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree129.table
  base := (25346367225324645227200494918983584801577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (287826)
      previous := (0)
      next := (234960)
      square := (7038739582727249712995609683660000000000000)
      linear := (-1027779691973144331962053408103980000000000000)
      constant := (38494546688811864733998885500649704876066457085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree129.table
  base := (63365918063045056819289936460530667760177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (584793)
      previous := (0)
      next := (472560)
      square := (14236097397434907717087004789430000000000000)
      linear := (-2087942486614237969999446904064390000000000000)
      constant := (78531353678736634696654077592865543125703831257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell161.Kernel129
