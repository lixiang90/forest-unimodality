import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell212.Parameters
import ForestUnimodality.BinomialMassData.Q53_93.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_93.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_187.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_187.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree000.table
  base := (88491632153280198275169257/5000000000000000000000000)
  polynomial :=
    { denominator := 155000000000000000000000000000000000000000
      center := (371)
      previous := (0)
      next := (280)
      square := (13372572420747866200896325505000000000000)
      linear := (-43388380828048895010429220600000000000000)
      constant := (2743240596751686146530246967000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree000.table
  base := (88491632153280198275169257/5000000000000000000000000)
  polynomial :=
    { denominator := 935000000000000000000000000000000000000000
      center := (2247)
      previous := (0)
      next := (1680)
      square := (80666807828382289663471382885000000000000)
      linear := (-261729910156294947320976266200000000000000)
      constant := (16547935212663397077456651059000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree001.table
  base := (14279113741352569691239789297391419162957/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-16357836280823463159794784057990000000000000)
      constant := (502110699158134590059574441070648537361660372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree001.table
  base := (28496394641303964639863113952036590266573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-66206190074500965137005437716790000000000000)
      constant := (2025924741766535151898802602470830050063582474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49476079170996267679/100000000000000000000)
  directionHi := (309225494818726673/625000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree002.table
  base := (74094346881568112679645268499872836030337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-41220628621242569223359631137160000000000000)
      constant := (678130837270452221511160467258560158826384713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree002.table
  base := (4611383243057678809341267573972379168377/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-83468886949774775124988313654180000000000000)
      constant := (1365809057610498535208373920960301017111802504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49476079170996267679/100000000000000000000)
  centralHi := (309225494818726673/625000000000000000)
  directionLo := (546638610755218117/781250000000000000)
  directionHi := (69969742176667918977/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree003.table
  base := (24131761641366675998758013365889884129791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-2762532482268789562618316342130000000000000)
      constant := (26701934731881281785143643999115178648729151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree003.table
  base := (9593577531137152138079008154622441142223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-201463167650097170225942379183140000000000000)
      constant := (1934317938965325165711301155073470721511980435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546638610755218117/781250000000000000)
  centralHi := (69969742176667918977/100000000000000000000)
  directionLo := (85695082883465794441/100000000000000000000)
  directionHi := (42847541441732897221/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree004.table
  base := (1574658145137663511151168306097380392919/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-29115270370216927515449878589760000000000000)
      constant := (183174834949856649742648642499082430183564310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree004.table
  base := (15622145188192256255051576414661689334781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-117994280700322395100954065528960000000000000)
      constant := (737331883933507863279663272136224614347956789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85695082883465794441/100000000000000000000)
  centralHi := (42847541441732897221/50000000000000000000)
  directionLo := (49476079170996267679/50000000000000000000)
  directionHi := (98952158341992535359/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree005.table
  base := (10233981182546362723171972072469769178279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-33367748400014748967334910100350000000000000)
      constant := (153300656272175230595616728399166033622935071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree005.table
  base := (4054303499766794506860395848982168220343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-270513955151192410177873882932700000000000000)
      constant := (1235865347098706456821034437544037202485871835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49476079170996267679/50000000000000000000)
  centralHi := (98952158341992535359/100000000000000000000)
  directionLo := (110631876286509095933/100000000000000000000)
  directionHi := (55315938143254547967/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree006.table
  base := (13094358487700401140432997941156527212777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-8360050317736126759826653691320000000000000)
      constant := (31475836127356968956442661490211422651478697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree006.table
  base := (3236368405878367487324092571284259424871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-152519674450870015076919817403740000000000000)
      constant := (572172282317279509406159571907098535656627998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110631876286509095933/100000000000000000000)
  centralHi := (55315938143254547967/50000000000000000000)
  directionLo := (15148893555310475399/12500000000000000000)
  directionHi := (121191148442483803193/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree007.table
  base := (321978752858812234045073467922370749929/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-83745408919220783742209946243060000000000000)
      constant := (284951697402982357648487013001224615403398025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree007.table
  base := (7939744330716995990320110221584597526609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-339564742652287650129805386682260000000000000)
      constant := (1153718034631873992038070865275901790907990121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15148893555310475399/12500000000000000000)
  centralHi := (121191148442483803193/100000000000000000000)
  directionLo := (65450700666499428779/50000000000000000000)
  directionHi := (130901401332998857559/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree008.table
  base := (281080515196404166503186857837584168323/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-46125182489408213322990004632120000000000000)
      constant := (152189110501791933288158919283178123774605016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree008.table
  base := (552257451498170101429531727227832888959/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-187045068201417635052885569278520000000000000)
      constant := (617371115582420983387860281978200353176029084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65450700666499428779/50000000000000000000)
  centralHi := (130901401332998857559/100000000000000000000)
  directionLo := (139939484353335837953/100000000000000000000)
  directionHi := (69969742176667918977/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree009.table
  base := (954710079215634674013077247275721795359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-5597517835467337197208337349190000000000000)
      constant := (18721777433557831661444813474286968645339999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree009.table
  base := (1853094723579860466091898110194946785681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-408615530153382890081736890431820000000000000)
      constant := (1368977135269664204718259776119597094148478889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139939484353335837953/100000000000000000000)
  centralHi := (69969742176667918977/50000000000000000000)
  directionLo := (74214118756494401519/50000000000000000000)
  directionHi := (148428237512988803039/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree010.table
  base := (-4816052703399266874791919184813895049/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-54630138549003856226760067653300000000000000)
      constant := (189952016381570713249026530478352723108605995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree010.table
  base := (-17543409579301445532912313642466520617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-443140923903930510057702642306600000000000000)
      constant := (1544793221545560936565022838168182941202720635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74214118756494401519/50000000000000000000)
  centralHi := (148428237512988803039/100000000000000000000)
  directionLo := (78228549937581783193/50000000000000000000)
  directionHi := (156457099875163566387/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree011.table
  base := (-1586641940395790387399921420523075493161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-117765233157603355357290198327780000000000000)
      constant := (431287771769230004663695053264885920059650511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree011.table
  base := (-161414974719008322787607650130474335017/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (38199)
      previous := (0)
      next := (28560)
      square := (1371335733082498924279013509045000000000000)
      linear := (-21712105347930824092439472462790000000000000)
      constant := (79766131882808971152463899393421110444904785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78228549937581783193/50000000000000000000)
  centralHi := (156457099875163566387/100000000000000000000)
  directionLo := (32818718141622532291/20000000000000000000)
  directionHi := (10255849419257041341/6250000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree012.table
  base := (-283957109192263292087802707845632499153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-7015010512066611014503347852720000000000000)
      constant := (27221564596138576060280214159121735841569835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree012.table
  base := (-1429273048952541215720314961485206473771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-256095855702512875004817073028080000000000000)
      constant := (997267141098328850178091522937503814818701901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32818718141622532291/20000000000000000000)
  centralHi := (10255849419257041341/6250000000000000000)
  directionLo := (85695082883465794441/50000000000000000000)
  directionHi := (171390165766931588883/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree013.table
  base := (-3891412823356971036118368856143879562221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-134775145276794641164830324370140000000000000)
      constant := (555274669230704063078868854114521585666350571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree013.table
  base := (-976103455709110595560145226299724792129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-273358552577786684992799948965470000000000000)
      constant := (1130455591155862885299466200719504847488081998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85695082883465794441/50000000000000000000)
  centralHi := (171390165766931588883/100000000000000000000)
  directionLo := (22298567544992863369/12500000000000000000)
  directionHi := (178388540359942906953/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree014.table
  base := (-4795598685311822938305954223989070414379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-143280101336390284068600387391320000000000000)
      constant := (626685161788607092188524921404358529986036029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree014.table
  base := (-960891161490649495615803819586399415501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-581242498906120989961565649805720000000000000)
      constant := (2552142634565033163775677611378455994196727655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22298567544992863369/12500000000000000000)
  centralHi := (178388540359942906953/100000000000000000000)
  directionLo := (23140317137346315901/12500000000000000000)
  directionHi := (185122537098770527209/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree015.table
  base := (-1117187071217446133884637748693648443073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-16865006377331769663596716712500000000000000)
      constant := (78214138493731821421434025670277019231034235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree015.table
  base := (-5591940021340888610391921883184657015591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-615767892656668609937531401680500000000000000)
      constant := (2867065291328148345803793982621665728821798321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23140317137346315901/12500000000000000000)
  centralHi := (185122537098770527209/100000000000000000000)
  directionLo := (191620030664908205183/100000000000000000000)
  directionHi := (1497031489569595353/781250000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree016.table
  base := (-3141908445712434447494417363083215588377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-80145006727790784938070256716840000000000000)
      constant := (393407943003766110354970503883013268376127327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree016.table
  base := (-6287870627788159713690962891929776982447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-650293286407216229913497153555280000000000000)
      constant := (3204944658015025481587342799967147628700810857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191620030664908205183/100000000000000000000)
  centralHi := (1497031489569595353/781250000000000000)
  directionLo := (197904316683985070717/100000000000000000000)
  directionHi := (98952158341992535359/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree017.table
  base := (-862848122033129427171535796355856969453/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-84397484757588606389955288227430000000000000)
      constant := (437616979223697970123468180589927772284804012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree017.table
  base := (-6905511635073928594009552744728176531243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (49434)
      previous := (0)
      next := (36960)
      square := (1774669772224410372596370423470000000000000)
      linear := (-40283451773986108817027229731180000000000000)
      constant := (209724523854127108401008336907324140875233149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197904316683985070717/100000000000000000000)
  centralHi := (98952158341992535359/50000000000000000000)
  directionLo := (203995100363439470387/100000000000000000000)
  directionHi := (50998775090859867597/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree018.table
  base := (-7451412839220972965148489870953671620023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-19699991730530317298186737719560000000000000)
      constant := (107678590434322401671605286849653521573157897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree018.table
  base := (-7453240992155616652501154822779600476711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-719344073908311469865428657304840000000000000)
      constant := (3947889065346462360516255304016580150929893041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203995100363439470387/100000000000000000000)
  centralHi := (50998775090859867597/25000000000000000000)
  directionLo := (209909226530003756929/100000000000000000000)
  directionHi := (20990922653000375693/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree019.table
  base := (-198378234398477788779156834113755934701/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-92902440817184249293725351248610000000000000)
      constant := (534194498936801635960672577300497498415421020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree019.table
  base := (-992043955688073682750019940095995316503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-376934733829429544920697204589810000000000000)
      constant := (2176238024224386425984118866015827559108826372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209909226530003756929/100000000000000000000)
  centralHi := (20990922653000375693/10000000000000000000)
  directionLo := (215661229228990354921/100000000000000000000)
  directionHi := (107830614614495177461/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree020.table
  base := (-8357373152613772615169833469134040457861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-194309837693964141491220765518400000000000000)
      constant := (1173049270182486224745281523497459684079960211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree020.table
  base := (-8358188298799098465951946185501932595321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-788394861409406709817360161054400000000000000)
      constant := (4778960893884167542447247541091182919074219951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215661229228990354921/100000000000000000000)
  centralHi := (107830614614495177461/50000000000000000000)
  directionLo := (110631876286509095933/50000000000000000000)
  directionHi := (221263752573018191867/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree021.table
  base := (-1090040326213392302113147749883314471583/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-11267488541864432466388379363310000000000000)
      constant := (71281627194666281063984079564103539171234948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree021.table
  base := (-8720865034049211875313755140790879457951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-822920255159954329793325912929180000000000000)
      constant := (5227269674318836356684320994311873736234911481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110631876286509095933/50000000000000000000)
  centralHi := (221263752573018191867/100000000000000000000)
  directionLo := (226727877890718381873/100000000000000000000)
  directionHi := (113363938945359190937/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree022.table
  base := (-564084887244016966866506458679281721427/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-105659874906577713649380445780380000000000000)
      constant := (699218558168723334730725218714243139131023016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree022.table
  base := (-2256429607073737133552384610803043404391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (38199)
      previous := (0)
      next := (28560)
      square := (1371335733082498924279013509045000000000000)
      linear := (-38974802223204634080422348400180000000000000)
      constant := (258970711408648494350876709646694250034882022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226727877890718381873/100000000000000000000)
  centralHi := (113363938945359190937/50000000000000000000)
  directionLo := (232063381477912615487/100000000000000000000)
  directionHi := (3625990335592384617/1562500000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree023.table
  base := (-9273354905685409215483096798561078494169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-219824705872751070202530954581940000000000000)
      constant := (1519145182855587482043508256788955232103932319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree023.table
  base := (-9273593718456947148483086841830658405487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-891971042661049569745257416678740000000000000)
      constant := (6189189266808581284647495876133333706218525097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232063381477912615487/100000000000000000000)
  centralHi := (3625990335592384617/1562500000000000000)
  directionLo := (237278940138179744651/100000000000000000000)
  directionHi := (59319735034544936163/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree024.table
  base := (-9464867499561154129725059434757110285087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-25369962436927412567366779733680000000000000)
      constant := (182798743437195477342587088176958417016031393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree024.table
  base := (-4732512783722639841286242047531159465243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-463248218205798594860611584276760000000000000)
      constant := (3351375912573238638472255217541002884659917533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237278940138179744651/100000000000000000000)
  centralHi := (59319735034544936163/25000000000000000000)
  directionLo := (48476459376993521277/20000000000000000000)
  directionHi := (121191148442483803193/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree025.table
  base := (-1920049560454372211562321152359618531811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-236834617991942356010071080624300000000000000)
      constant := (1776564597642782782524455303904958296591833305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree025.table
  base := (-9600352277128597532262121957313174136121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-961021830162144809697188920428300000000000000)
      constant := (7238031495925909981951146893813465613633984751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48476459376993521277/20000000000000000000)
  centralHi := (121191148442483803193/50000000000000000000)
  directionLo := (247380395854981338397/100000000000000000000)
  directionHi := (123690197927490669199/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree026.table
  base := (-9679719003604558683001298699522890976229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-245339574051537998913841143645480000000000000)
      constant := (1913270972611189930285519477032266515946595379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree026.table
  base := (-2419946991996471059136191788084954038407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-497773611956346214836577336151540000000000000)
      constant := (3897510395783924912146183596382334484461891234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247380395854981338397/100000000000000000000)
  centralHi := (123690197927490669199/50000000000000000000)
  directionLo := (252279493148971501729/100000000000000000000)
  directionHi := (25227949314897150173/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree027.table
  base := (-485171136713491190308829527488185328433/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-14102473895062980100978400370370000000000000)
      constant := (114183699493109164478646887945333538993758870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree027.table
  base := (-9703468205738501602396026087888627169487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1030072617663240049649120424177860000000000000)
      constant := (8373714971474586502940041351463132596510209097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252279493148971501729/100000000000000000000)
  centralHi := (25227949314897150173/10000000000000000000)
  directionLo := (64271312162599345831/25000000000000000000)
  directionHi := (10283409946015895333/4000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree028.table
  base := (-386857955989673341025067818091429277481/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-262349486170729284721381269687840000000000000)
      constant := (2202670674844661715791725408761340704476670775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree028.table
  base := (-9671478850279548297911883399567453535601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1064598011413787669625086176052640000000000000)
      constant := (8974111033211518250569520883186285717313568631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64271312162599345831/25000000000000000000)
  centralHi := (10283409946015895333/4000000000000000000)
  directionLo := (65450700666499428779/25000000000000000000)
  directionHi := (261802802665997715117/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree029.table
  base := (-4791927295949332499276029272475325878001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-135427221115162463812575666354510000000000000)
      constant := (1177681365364813353240568552135455906481169351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree029.table
  base := (-4791937150510016325037208537553313470547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-549561702582167644800525963963710000000000000)
      constant := (4798103537242820758497284751390593181248441957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65450700666499428779/25000000000000000000)
  centralHi := (261802802665997715117/100000000000000000000)
  directionLo := (133218420173324783967/50000000000000000000)
  directionHi := (53287368069329913587/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree030.table
  base := (-9440676080204945892575262625041616961577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-31039933143324507836546821747800000000000000)
      constant := (279264716092917818665179038992335006099924503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree030.table
  base := (-2360172259776092344263488067155695822563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-566824399457441454788508839901100000000000000)
      constant := (5120000944762908631967744554966764945561588906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133218420173324783967/50000000000000000000)
  centralHi := (53287368069329913587/20000000000000000000)
  directionLo := (270991646188661545947/100000000000000000000)
  directionHi := (67747911547165386487/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree031.table
  base := (-9241936416921389554003586375567689406173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2790000000000000000000000000000000000000000
      center := (6678)
      previous := (0)
      next := (5040)
      square := (240706303573461591616133859090000000000000)
      linear := (-9285946914500523013957788991980000000000000)
      constant := (86346116702759993244385048239106614655677733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree031.table
  base := (-9241944931137764508094626612138717241819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1168174192665430529552983431676980000000000000)
      constant := (10905494713678728041755641455789111196770831389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270991646188661545947/100000000000000000000)
  centralHi := (67747911547165386487/25000000000000000000)
  directionLo := (275471150420829753553/100000000000000000000)
  directionHi := (137735575210414876777/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree032.table
  base := (-449382513095834104675682323390312812247/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-148184655204555928168230760886280000000000000)
      constant := (1422702061392160354038935240062451844868756970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree032.table
  base := (-4493827926083045969525975382580104502771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-601349793207989074764474591775880000000000000)
      constant := (5796342530873947343095427594047836325642600901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275471150420829753553/100000000000000000000)
  centralHi := (137735575210414876777/50000000000000000000)
  directionLo := (139939484353335837953/50000000000000000000)
  directionHi := (279878968706671675907/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree033.table
  base := (-4338913472221938062045071334253104653881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-16937459248261527735568421377430000000000000)
      constant := (167744771063546303802372702043677766427620359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree033.table
  base := (-8677830612694323562639418046249985658263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (76398)
      previous := (0)
      next := (57120)
      square := (2742671466164997848558027018090000000000000)
      linear := (-112474998196956888136810448675140000000000000)
      constant := (1118324784148978985011348378090581295592381923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139939484353335837953/50000000000000000000)
  centralHi := (279878968706671675907/100000000000000000000)
  directionLo := (35527304537857919311/12500000000000000000)
  directionHi := (284218436302863354489/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree034.table
  base := (-8312472406684966223747688827685992610681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-313379222528303142144001647814920000000000000)
      constant := (3198734835470166000565202570207383849910220031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree034.table
  base := (-1662494962494064650914594584097113088901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (49434)
      previous := (0)
      next := (36960)
      square := (1774669772224410372596370423470000000000000)
      linear := (-74808845524533728792992981605960000000000000)
      constant := (766597482913751025687509500381881191880653215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35527304537857919311/12500000000000000000)
  centralHi := (284218436302863354489/100000000000000000000)
  directionLo := (36061579698954598739/12500000000000000000)
  directionHi := (288492637591636789913/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree035.table
  base := (-1972897609460959096102721854410841541469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-160942089293949392523885855418050000000000000)
      constant := (1691695479495246955899598196802776263015669238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree035.table
  base := (-1972898003728870282033323255175084450897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-653137883833810504728423219588050000000000000)
      constant := (6892219344411803950004015607219939943673165614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36061579698954598739/12500000000000000000)
  centralHi := (288492637591636789913/100000000000000000000)
  directionLo := (58540886346113406079/20000000000000000000)
  directionHi := (73176107932641757599/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree036.table
  base := (-370759172900303313244206342270115364173/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-18354951924860801552863431880960000000000000)
      constant := (198520790487416501315316163980464191350297470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree036.table
  base := (-7415184491402923246392561845372808706043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1340801161418168629432812191050880000000000000)
      constant := (14558416984080643379786370098081798252358382333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58540886346113406079/20000000000000000000)
  centralHi := (73176107932641757599/25000000000000000000)
  directionLo := (74214118756494401519/25000000000000000000)
  directionHi := (296856475025977606077/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree037.table
  base := (-6883253016187363233011885792024627349533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-338894090707090070855311836878460000000000000)
      constant := (3768684631421738483170199348223288998053889083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree037.table
  base := (-1720813423272697906371097406862891307053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-687663277584358124704388971462830000000000000)
      constant := (7677046022279662403930250970590878107767327286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74214118756494401519/25000000000000000000)
  centralHi := (296856475025977606077/100000000000000000000)
  directionLo := (300951240527404300753/100000000000000000000)
  directionHi := (150475620263702150377/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree038.table
  base := (-1573950026722999457238428341600064786249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-173699523383342856879540949949820000000000000)
      constant := (1984661079166875427190440821543782079327464798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree038.table
  base := (-3147900275072256224688400174501570041719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-704925974459631934692371847400220000000000000)
      constant := (8085731918866348698001624456555434597211128289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300951240527404300753/100000000000000000000)
  centralHi := (150475620263702150377/50000000000000000000)
  directionLo := (15249551762684555017/5000000000000000000)
  directionHi := (304991035253691100341/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree039.table
  base := (-1130565074277878816257239118570868769369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-39544889202920150740316884768980000000000000)
      constant := (463920755995910543209397660412976975563181955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree039.table
  base := (-5652825661564518340372095321048192836839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1444377342669811489360709446675220000000000000)
      constant := (17010532342654315015845321839324055744688577009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15249551762684555017/5000000000000000000)
  centralHi := (304991035253691100341/100000000000000000000)
  directionLo := (308978015391472372497/100000000000000000000)
  directionHi := (154489007695736186249/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree040.table
  base := (-990865845148121066676790175787116229373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-364408958885876999566622025942000000000000000)
      constant := (4386578564711558536314444175504086158660764615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree040.table
  base := (-1238582353915274174359700620384499870167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-739451368210179554668337599275000000000000000)
      constant := (8935648772872677613666095133179548848080260354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308978015391472372497/100000000000000000000)
  centralHi := (154489007695736186249/50000000000000000000)
  directionLo := (312914199750327132773/100000000000000000000)
  directionHi := (156457099875163566387/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree041.table
  base := (-1050077985566564058697796862674285286097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-186456957472736321235196044481590000000000000)
      constant := (2301598719111770357038284740751155213121094094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree041.table
  base := (-2100156033273393318956327194747401303453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-756714065085453364656320475212390000000000000)
      constant := (9376879719059878325034870481179773123819552043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312914199750327132773/100000000000000000000)
  centralHi := (156457099875163566387/50000000000000000000)
  directionLo := (9900046303529772653/3125000000000000000)
  directionHi := (316801481712952724897/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree042.table
  base := (-1695386850705637878500197628599025499253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-21189937278059349187453452888020000000000000)
      constant := (268063523496581846194250906452336336495217867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree042.table
  base := (-3390773782726113892512308022100030225209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1547953523921454349288606702299560000000000000)
      constant := (19657918013885084523780473211490344043054666479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9900046303529772653/3125000000000000000)
  centralHi := (316801481712952724897/100000000000000000000)
  directionLo := (160320819940562469117/50000000000000000000)
  directionHi := (64128327976224987647/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree043.table
  base := (-2525714624780406735201534516674649228189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-389923827064663928277932215005540000000000000)
      constant := (5052416517804596667792726713495790958825393339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree043.table
  base := (-505142935595470054334011417586744392631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1582478917672001969264572454174340000000000000)
      constant := (20583773269062626461525380135056155676670432805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160320819940562469117/50000000000000000000)
  centralHi := (64128327976224987647/20000000000000000000)
  directionLo := (162218173793653358663/50000000000000000000)
  directionHi := (324436347587306717327/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree044.table
  base := (-401283699048221892217555878100678955953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-199214391562129785590851139013360000000000000)
      constant := (2642508361048479215024068025515734455419925006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree044.table
  base := (-802567415495972997362680717941655034233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (38199)
      previous := (0)
      next := (28560)
      square := (1371335733082498924279013509045000000000000)
      linear := (-73500195973752254056388100274960000000000000)
      constant := (978696600040937324572017280072783478646173293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162218173793653358663/50000000000000000000)
  centralHi := (324436347587306717327/100000000000000000000)
  directionLo := (32818718141622532291/10000000000000000000)
  directionHi := (328187181416225322911/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree045.table
  base := (-125806855022179365754749854469391856743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-45214859909317246009496926783100000000000000)
      constant := (613660448366807792867130895916024572128349885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree045.table
  base := (-629034297873665386141582166195880557063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1651529705173097209216503957923900000000000000)
      constant := (22500573807437176026295314016811046252800063953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32818718141622532291/10000000000000000000)
  centralHi := (328187181416225322911/100000000000000000000)
  directionLo := (331895628859527287799/100000000000000000000)
  directionHi := (1659478144297636439/500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree046.table
  base := (402586894788391014264552100171142708957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-415438695243450856989242404069080000000000000)
      constant := (5766198457039767903062701716176420213289769093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree046.table
  base := (201293439949594320499714486117766255717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-843027549461822414596234854899340000000000000)
      constant := (11745759543610918172045311213439272168196167773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331895628859527287799/100000000000000000000)
  centralHi := (1659478144297636439/500000000000000000)
  directionLo := (335563095208927546629/100000000000000000000)
  directionHi := (33556309520892754663/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree047.table
  base := (1489728680134679367633857299841587220563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-423943651303046499893012467090260000000000000)
      constant := (6014779987023832036594215999060439887870649387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree047.table
  base := (1489728670395604109090662800616257631603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1720580492674192449168435461673460000000000000)
      constant := (24504161039138006536125365887830459913119525307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335563095208927546629/100000000000000000000)
  centralHi := (33556309520892754663/10000000000000000000)
  directionLo := (42398863722305854997/12500000000000000000)
  directionHi := (339190909778446839977/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree048.table
  base := (2632391054358485021300789746703537753271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-48049845262515793644086947790160000000000000)
      constant := (696520958335962564012793581984022099780893431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree048.table
  base := (2632391047987972579544628266258908906581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1755105886424740069144401213548240000000000000)
      constant := (25538499662289514762910578425045367785554230989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42398863722305854997/12500000000000000000)
  centralHi := (339190909778446839977/100000000000000000000)
  directionLo := (68556066306772635553/20000000000000000000)
  directionHi := (171390165766931588883/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree049.table
  base := (3830573995442755307565856863756613886283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-440953563422237785700552593132620000000000000)
      constant := (6527924370848835533102547521265220953502461667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree049.table
  base := (38305739912754907479572561983044965449/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-894815640087643844560183482711510000000000000)
      constant := (13297267477963998166847277071843749969839304050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68556066306772635553/20000000000000000000)
  centralHi := (171390165766931588883/50000000000000000000)
  directionLo := (86583138549243468439/25000000000000000000)
  directionHi := (346332554196973873757/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree050.table
  base := (1271069371119271417646861015624800153361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-224729259740916714302161328076900000000000000)
      constant := (3396243612167896659276478862355777793052838578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree050.table
  base := (2542138740875445530427497789452678657013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-912078336962917654548166358648900000000000000)
      constant := (13836133459703135304699938219106870719957087597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86583138549243468439/25000000000000000000)
  centralHi := (346332554196973873757/100000000000000000000)
  directionLo := (174924355441669797441/50000000000000000000)
  directionHi := (349848710883339594883/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree051.table
  base := (31967507523622584210085594747535709013/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-25442415307857170639338484398610000000000000)
      constant := (392354288074432137319690403134693181636149300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree051.table
  base := (6393501502940906066691037924514294185657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (49434)
      previous := (0)
      next := (36960)
      square := (1774669772224410372596370423470000000000000)
      linear := (-109334239275081348768958733480740000000000000)
      constant := (1692452679538134347089023821338995903139896449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174924355441669797441/50000000000000000000)
  centralHi := (349848710883339594883/100000000000000000000)
  directionLo := (353329878324589508567/100000000000000000000)
  directionHi := (44166234790573688571/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree052.table
  base := (7758246041016001230781666841946449632923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-466468431601024714411862782196160000000000000)
      constant := (7337594253729593900091763882612154842875151027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree052.table
  base := (1551649207969790749456882199607091658279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1893207461426930549048264221047360000000000000)
      constant := (29892820853629620730441369299176061940991791755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353329878324589508567/100000000000000000000)
  centralHi := (44166234790573688571/12500000000000000000)
  directionLo := (71355416143977162781/20000000000000000000)
  directionHi := (178388540359942906953/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree053.table
  base := (4589255539677293873778447376304926384527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-237486693830310178657816422608670000000000000)
      constant := (3809069214692089986796701329064116308299774023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree053.table
  base := (9178511078590876231582159113592124440983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1927732855177478169024229972922140000000000000)
      constant := (31035642823364765982590918640073712999576734527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71355416143977162781/20000000000000000000)
  centralHi := (178388540359942906953/50000000000000000000)
  directionLo := (72038258651119158901/20000000000000000000)
  directionHi := (180095646627797897253/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree054.table
  base := (5327148303327023452089549130180514826547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-26859907984456444456633494902140000000000000)
      constant := (439111650677241882967567539079683474748311667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree054.table
  base := (10654296606154209065091328613735549776887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-1962258248928025789000195724796920000000000000)
      constant := (32200161460898686787452888889008558440147961503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72038258651119158901/20000000000000000000)
  centralHi := (180095646627797897253/50000000000000000000)
  directionLo := (363573445327451409577/100000000000000000000)
  directionHi := (181786722663725704789/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree055.table
  base := (304640065264096594032347395802105564311/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-245991649889905821561586485629850000000000000)
      constant := (4097604051020648027924863486325223220514516780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree055.table
  base := (12185602610236678324707776168863373943681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (76398)
      previous := (0)
      next := (57120)
      square := (2742671466164997848558027018090000000000000)
      linear := (-181525785698052128088741952424700000000000000)
      constant := (3035125160527380448019113750717066665766961899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363573445327451409577/100000000000000000000)
  centralHi := (181786722663725704789/50000000000000000000)
  directionLo := (366924423495367762271/100000000000000000000)
  directionHi := (11466388234230242571/3125000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree056.table
  base := (1721553634918734805629494461967496594147/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-250244127919703643013471517140440000000000000)
      constant := (4245866799417758856072437605640147512171109612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree056.table
  base := (6886214539567836775265628339422005006733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1015654518214560514476063614273240000000000000)
      constant := (17297144368831515909845377037902368093080446277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366924423495367762271/100000000000000000000)
  centralHi := (11466388234230242571/3125000000000000000)
  directionLo := (23140317137346315901/6250000000000000000)
  directionHi := (370245074197541054417/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree057.table
  base := (15414776001810926224003748737899245941771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-56554801322111436547857010811340000000000000)
      constant := (977065133608459998726640954891311175350041931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree057.table
  base := (1541477600167066408436862808683513929349/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1032917215089834324464046490210630000000000000)
      constant := (17911948688046627742654020679086923992977025905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23140317137346315901/6250000000000000000)
  centralHi := (370245074197541054417/100000000000000000000)
  directionLo := (373536206247369508439/100000000000000000000)
  directionHi := (9338405156184237711/2500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree058.table
  base := (17112643367218897567334174275196698006457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-517498167958598571834483160323240000000000000)
      constant := (9100765912870375465701972163064536241057846593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree058.table
  base := (17112643367127036444520632853294327138791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2100359823930216268904058732296040000000000000)
      constant := (37075202680717176606220571768094809325716382479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373536206247369508439/100000000000000000000)
  centralHi := (9338405156184237711/2500000000000000000)
  directionLo := (188399296567033433093/50000000000000000000)
  directionHi := (376798593134066866187/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree059.table
  base := (18866031165274153304131442712671877727423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-526003124018194214738253223344420000000000000)
      constant := (9413272729929142564442408234201689070464481527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree059.table
  base := (18866031165213979512272161714409323389829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2134885217680763888880024484170820000000000000)
      constant := (38348204651174935808417996649721369629618930301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188399296567033433093/50000000000000000000)
  centralHi := (376798593134066866187/100000000000000000000)
  directionLo := (5938015236648571783/1562500000000000000)
  directionHi := (380032975145508594113/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree060.table
  base := (20674939386071115220724908338930780217751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-59389786675309984182447031818400000000000000)
      constant := (1081234072618529770976782154741712479789258711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree060.table
  base := (20674939386031690281648724774964234909583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2169410611431311508855990236045600000000000000)
      constant := (39642903287120346880584394065907724330553207927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5938015236648571783/1562500000000000000)
  centralHi := (380032975145508594113/100000000000000000000)
  directionLo := (191620030664908205183/50000000000000000000)
  directionHi := (383240061329816410367/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree061.table
  base := (22539368020070697472822778557928025363499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-543013036137385500545793349386780000000000000)
      constant := (10054267683700748035280585924322509491368902851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree061.table
  base := (22539368020044861431864348132863422855207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2203936005181859128831955987920380000000000000)
      constant := (40959298588219969661019199295271491033823733583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191620030664908205183/50000000000000000000)
  centralHi := (383240061329816410367/100000000000000000000)
  directionLo := (193210265655202786827/50000000000000000000)
  directionHi := (77284106262081114731/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree062.table
  base := (191088414516229882413881297198180874261/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1395000000000000000000000000000000000000000
      center := (3339)
      previous := (0)
      next := (2520)
      square := (120353151786730795808066929545000000000000)
      linear := (-8895451487048082958863926006580000000000000)
      constant := (167463803552444374026969869967750717690804416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree062.table
  base := (24459317058060490345294585340593243531039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2238461398932406748807921739795160000000000000)
      constant := (42297390554152334041186703069989565133036902791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193210265655202786827/50000000000000000000)
  centralHi := (77284106262081114731/20000000000000000000)
  directionLo := (194787518483828183539/50000000000000000000)
  directionHi := (389575036967656367079/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree063.table
  base := (26434786491219841062032031117145185206401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-62224772028508531817037052825460000000000000)
      constant := (1190730118126938685993708243056166522983351361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree063.table
  base := (26434786491208738563584977366418204001251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2272986792682954368783887491669940000000000000)
      constant := (43657179184607270640036708312181188175719746219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194787518483828183539/50000000000000000000)
  centralHi := (389575036967656367079/100000000000000000000)
  directionLo := (15708168159959862907/4000000000000000000)
  directionHi := (98176050999749143169/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree064.table
  base := (5693155262186658497301830063279833364643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-568527904316172429257103538450320000000000000)
      constant := (11055713412299363301482242177135176393853986535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree064.table
  base := (28465776310926011920945198471981526274049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2307512186433501988759853243544720000000000000)
      constant := (45038664479285319133185693121101761992277219481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15708168159959862907/4000000000000000000)
  centralHi := (98176050999749143169/25000000000000000000)
  directionLo := (79161726673594028287/20000000000000000000)
  directionHi := (98952158341992535359/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree065.table
  base := (7638071627236122472218293398408652133713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-288516430187884036080436800735750000000000000)
      constant := (5700091433825370446421495888993047864608967474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree065.table
  base := (6110457301787942897292667606114303973281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2342037580184049608735818995419500000000000000)
      constant := (46441846437897195113525598894045805478208316445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79161726673594028287/20000000000000000000)
  centralHi := (98952158341992535359/25000000000000000000)
  directionLo := (79777780530359428443/20000000000000000000)
  directionHi := (49861112831474642777/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree066.table
  base := (32694317077257444189626004734788002898261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-65059757381707079451627073832520000000000000)
      constant := (1305553269903047070941893772878091270785228821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree066.table
  base := (8173579269313577804062866974676505690137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (38199)
      previous := (0)
      next := (28560)
      square := (1371335733082498924279013509045000000000000)
      linear := (-108025589724299874032353852149740000000000000)
      constant := (2175760230007422850732123121443813223177891046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79777780530359428443/20000000000000000000)
  centralHi := (49861112831474642777/12500000000000000000)
  directionLo := (50243195911997873339/12500000000000000000)
  directionHi := (401945567295982986713/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree067.table
  base := (34891868008140507283075110248882330848399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-594042772494959357968413727513860000000000000)
      constant := (12105103096662540513918263988721893279507802951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree067.table
  base := (17445934004069225681096389093545805016349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1205544183842572424343875249584530000000000000)
      constant := (24656650172906642168309062864618658255616708181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50243195911997873339/12500000000000000000)
  centralHi := (401945567295982986713/100000000000000000000)
  directionLo := (404979161783695086267/100000000000000000000)
  directionHi := (101244790445923771567/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree068.table
  base := (37144939294114329956742701774342316148707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-602547728554555000872183790535040000000000000)
      constant := (12465553870191402627827931484904046692370166843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree068.table
  base := (3714493929411298049728399078882448594117/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10285000000000000000000000000000000000000000
      center := (24717)
      previous := (0)
      next := (18480)
      square := (887334886112205186298185211735000000000000)
      linear := (-71929816512814484372462242677760000000000000)
      constant := (1493575655723105924232410953951345983790493345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404979161783695086267/100000000000000000000)
  centralHi := (101244790445923771567/25000000000000000000)
  directionLo := (203995100363439470387/50000000000000000000)
  directionHi := (16319608029075157631/4000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree069.table
  base := (1972676546397030216645553151460662190253/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-33947371367452813543108547419790000000000000)
      constant := (712851763869522547520648106462591963648331330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree069.table
  base := (39453530927939718365936199193351657469511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2480139155186240088639682002918620000000000000)
      constant := (52271540906227142052600560315321704110051330159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203995100363439470387/50000000000000000000)
  centralHi := (16319608029075157631/4000000000000000000)
  directionLo := (41097917988542151951/10000000000000000000)
  directionHi := (410979179885421519511/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree070.table
  base := (41817642902611493955094904165095536878841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-619557640673746286679723916577400000000000000)
      constant := (13202436734981939419037326011090911298465095809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree070.table
  base := (41817642902610912147083266044568896866699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2514664548936787708615647754793400000000000000)
      constant := (53783206180492852114314027614959529754531597331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41097917988542151951/10000000000000000000)
  centralHi := (410979179885421519511/100000000000000000000)
  directionLo := (25871661070004849911/6250000000000000000)
  directionHi := (413946577120077598577/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree071.table
  base := (8847455042267935671555516539350328503629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-628062596733341929583493979598580000000000000)
      constant := (13578868826124299784118658328341994956139436105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree071.table
  base := (5529659401417412024604358674511190044187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1274594971343667664295806753334090000000000000)
      constant := (27658284058572693858370586832558022218620700812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25871661070004849911/6250000000000000000)
  centralHi := (413946577120077598577/100000000000000000000)
  directionLo := (416892853284345762663/100000000000000000000)
  directionHi := (52111606660543220333/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree072.table
  base := (11678106961887238719711316501129825258239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-35364864044052087360403557923320000000000000)
      constant := (775590445723422742988391129430691524146335358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree072.table
  base := (46712427847548703795986663580231615282029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2583715336437882948567579258542960000000000000)
      constant := (56871626715954786885878141702138079354797272101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416892853284345762663/100000000000000000000)
  centralHi := (52111606660543220333/12500000000000000000)
  directionLo := (419818453060007513859/100000000000000000000)
  directionHi := (20990922653000375693/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree073.table
  base := (12310775201216337837961521489484624470989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-322536254426266607695517052820470000000000000)
      constant := (7173857162809369851393414903930960034099167722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree073.table
  base := (49243100804865186348979676659719817506759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2618240730188430568543545010417740000000000000)
      constant := (58448381976698159013286830036351052298393855471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419818453060007513859/100000000000000000000)
  centralHi := (20990922653000375693/5000000000000000000)
  directionLo := (84544761148123760727/20000000000000000000)
  directionHi := (105680951435154700909/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree074.table
  base := (51829294077108710915048725351827638376909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-653577464912128858294804168662120000000000000)
      constant := (14740127733862238594408912600162797244321885941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree074.table
  base := (51829294077108602455234324502255062068603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2652766123938978188519510762292520000000000000)
      constant := (60046833899159390734330371190232597265476978307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84544761148123760727/20000000000000000000)
  centralHi := (105680951435154700909/25000000000000000000)
  directionLo := (212804662983431306277/50000000000000000000)
  directionHi := (85121865193372522511/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree075.table
  base := (54471007658284715630610518636185072060529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-73564713441302722355397136853700000000000000)
      constant := (1681985360855584576979209721368123854250168369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree075.table
  base := (13617751914571161080242149968150030838767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1343645758844762904247738257083650000000000000)
      constant := (30833491241564433549884001076386851856801686446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212804662983431306277/50000000000000000000)
  centralHi := (85121865193372522511/20000000000000000000)
  directionLo := (428475414417328972207/100000000000000000000)
  directionHi := (26779713401083060763/6250000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree076.table
  base := (14292060385644329912456669473292204082371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-335293688515660072051172147352240000000000000)
      constant := (7770467933541252258726653386805728546216853558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree076.table
  base := (14292060385644318188651377969067068249321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1360908455720036714235721133021040000000000000)
      constant := (31654413864201603517554733564692532619221012098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428475414417328972207/100000000000000000000)
  centralHi := (26779713401083060763/6250000000000000000)
  directionLo := (215661229228990354921/50000000000000000000)
  directionHi := (431322458457980709843/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree077.table
  base := (11984199144868313151982828399788342766131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-679092333090915787006114357725660000000000000)
      constant := (15949330591960145333396809748397756882921335095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree077.table
  base := (7490124465542691864152835434566012684029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (38199)
      previous := (0)
      next := (28560)
      square := (1371335733082498924279013509045000000000000)
      linear := (-125288286599573684020336728087130000000000000)
      constant := (2953289528853864190199573341703146417290112764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215661229228990354921/50000000000000000000)
  centralHi := (431322458457980709843/100000000000000000000)
  directionLo := (217075416376642697151/50000000000000000000)
  directionHi := (434150832753285394303/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree078.table
  base := (7841158774762095201026809499837932016283/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-38199849397250634994993578930380000000000000)
      constant := (909058467904765618471402978485997010670591852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree078.table
  base := (62729270198096741313318120044532729941117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2790867698941168668423373769791640000000000000)
      constant := (66657608202082628317062860066850025033310920373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217075416376642697151/50000000000000000000)
  centralHi := (434150832753285394303/100000000000000000000)
  directionLo := (218480449920871568033/50000000000000000000)
  directionHi := (436960899841743136067/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree079.table
  base := (65593064958519993918401713913649493421261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-696102245210107072813654483768020000000000000)
      constant := (16782101358013374037791695086911344468600486389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree079.table
  base := (65593064958519980562851944112130936821679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2825393092691716288399339521666420000000000000)
      constant := (68364543430109918544657964302343696729717292951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218480449920871568033/50000000000000000000)
  centralHi := (436960899841743136067/100000000000000000000)
  directionLo := (439753010678313113649/100000000000000000000)
  directionHi := (8795060213566262273/2000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree080.table
  base := (3425619000021998035947906374198029190969/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-352303600634851357858712273394600000000000000)
      constant := (8603238699549098729282238669584387544726908810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree080.table
  base := (68512380000439951928091433491440515838543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2859918486442263908375305273541200000000000000)
      constant := (70093175318686047651818026661762183398358010167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439753010678313113649/100000000000000000000)
  centralHi := (8795060213566262273/2000000000000000000)
  directionLo := (110631876286509095933/25000000000000000000)
  directionHi := (442527505146036383733/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree081.table
  base := (71487215318831103081391043926977375406659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-79234684147699817624577178867820000000000000)
      constant := (1959575616166309481736785249180335257765799299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree081.table
  base := (71487215318831097293840427088925616892541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2894443880192811528351271025415980000000000000)
      constant := (71843503867635276896812752587825629897115266229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110631876286509095933/25000000000000000000)
  centralHi := (442527505146036383733/100000000000000000000)
  directionLo := (89056942507793281823/20000000000000000000)
  directionHi := (111321178134741602279/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree082.table
  base := (37258785454404009585264338604918375569861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-360808556694447000762482336415780000000000000)
      constant := (9035605398583441914259532009937919030303727789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree082.table
  base := (37258785454404007679719442130751757785371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1464484636971679574163618388645380000000000000)
      constant := (36807764538393384340779680559643038217996638499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89056942507793281823/20000000000000000000)
  centralHi := (111321178134741602279/25000000000000000000)
  directionLo := (224012476009174899447/50000000000000000000)
  directionHi := (89604990403669959779/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree083.table
  base := (19400861691405036144878408259722648400993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-365061034724244822214367367926370000000000000)
      constant := (9255784077033702652836779033840737372040376914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree083.table
  base := (77603446765620142069403213369217898560583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2963494667693906768303202529165540000000000000)
      constant := (75409250945974400531601646540085890694765026927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224012476009174899447/50000000000000000000)
  centralHi := (89604990403669959779/20000000000000000000)
  directionLo := (225374266521923111429/50000000000000000000)
  directionHi := (450748533043846222859/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree084.table
  base := (80744842884646683983673011866874822654361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (829099490086367704455572181310000000000000)
      linear := (-82069669500898365259167199874880000000000000)
      constant := (2106361401795376056481272608650626704570840921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree084.table
  base := (16148968576929336466019789450233383373571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-2998020061444454388279168281040320000000000000)
      constant := (77224669475036587863310305168075495915952021495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225374266521923111429/50000000000000000000)
  centralHi := (450748533043846222859/100000000000000000000)
  directionLo := (453455755781436763747/100000000000000000000)
  directionHi := (113363938945359190937/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree085.table
  base := (83941759261391780118418132395457860739547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-747131981567680930236274861895100000000000000)
      constant := (19408264183400936767011322745849065037536342003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree085.table
  base := (20985439815347944757221839510367745105919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10285000000000000000000000000000000000000000
      center := (24717)
      previous := (0)
      next := (18480)
      square := (887334886112205186298185211735000000000000)
      linear := (-89192513388088294360445118615150000000000000)
      constant := (2325346607759297501450396274368027903365750766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453455755781436763747/100000000000000000000)
  centralHi := (113363938945359190937/25000000000000000000)
  directionLo := (45614691148954271059/10000000000000000000)
  directionHi := (456146911489542710591/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree086.table
  base := (87194195891479906979779031470029682919173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-755636937627276573140044924916280000000000000)
      constant := (19864602855757218157304829660337526727567927277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree086.table
  base := (21798548972869976565439089178311860500253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1533535424472774814115549892394940000000000000)
      constant := (40460298256079987162136876140108594899666694314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45614691148954271059/10000000000000000000)
  centralHi := (456146911489542710591/100000000000000000000)
  directionLo := (458822282884760733633/100000000000000000000)
  directionHi := (229411141442380366817/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree087.table
  base := (45251076385325737485917788288688414103761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-42452327427048456446878610440970000000000000)
      constant := (1129237146288354860488714499734124565953714321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree087.table
  base := (9050215277065147449855644153920266525117/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1550798121348048624103532768332330000000000000)
      constant := (41400552509959606050955672048643244000584081865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458822282884760733633/100000000000000000000)
  centralHi := (229411141442380366817/50000000000000000000)
  directionLo := (11537053612212860313/2500000000000000000)
  directionHi := (461482144488514412521/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree088.table
  base := (93865629894758636490654846775685312635987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-772646849746467858947585050958640000000000000)
      constant := (20793261515664570027561000917253462268988651563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree088.table
  base := (93865629894758636178640335588310377034561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (76398)
      previous := (0)
      next := (57120)
      square := (2742671466164997848558027018090000000000000)
      linear := (-285101966949694988016639208049040000000000000)
      constant := (7700300926086252936443452195701798688592869419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11537053612212860313/2500000000000000000)
  centralHi := (461482144488514412521/100000000000000000000)
  directionLo := (18565070518233009239/4000000000000000000)
  directionHi := (3625990335592384617/781250000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree089.table
  base := (19456925451952256229071268593447378804017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-781151805806063501851355113979820000000000000)
      constant := (21265581503144822858826523989759021896379715165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree089.table
  base := (24321156814940320234905342671534347255741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1585323515098596244079498520207110000000000000)
      constant := (43313606006553703150955671523562664178372014058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18565070518233009239/4000000000000000000)
  centralHi := (3625990335592384617/781250000000000000)
  directionLo := (466756397387317525581/100000000000000000000)
  directionHi := (233378198693658762791/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree090.table
  base := (5037957243086160523925988737484835018319/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-43869820103647730264173620944500000000000000)
      constant := (1207957144199838989007511228946729264526045590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree090.table
  base := (100759144861723210342840040268629931785189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-3205172423947740108134962792289000000000000000)
      constant := (88572810498257439181809966495464720084596274141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466756397387317525581/100000000000000000000)
  centralHi := (233378198693658762791/50000000000000000000)
  directionLo := (11734282490637267479/2500000000000000000)
  directionHi := (469371299625490699161/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree091.table
  base := (104289182696808482664492175462592893159761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-798161717925254787658895240022180000000000000)
      constant := (22226202792988229796636962802453355932938772889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree091.table
  base := (52144591348404241287499182297739088894307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1619848908849143864055464272081890000000000000)
      constant := (45270052821132370945652313722099533199545021483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11734282490637267479/2500000000000000000)
  centralHi := (469371299625490699161/100000000000000000000)
  directionLo := (117992928634054394779/25000000000000000000)
  directionHi := (471971714536217579117/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree092.table
  base := (107874740761277918238858666576192909594623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-806666673984850430562665303043360000000000000)
      constant := (22714504095285866679144081749592052475083894327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree092.table
  base := (53937370380638959089909779415169289657981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1637111605724417674043447148019280000000000000)
      constant := (46264548722499279531994391502193134890049937589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117992928634054394779/25000000000000000000)
  centralHi := (471971714536217579117/100000000000000000000)
  directionLo := (237278940138179744651/50000000000000000000)
  directionHi := (474557880276359489303/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree093.table
  base := (111515819051485758448610513035808210043207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 310000000000000000000000000000000000000000
      center := (742)
      previous := (0)
      next := (560)
      square := (26745144841495732401792651010000000000000)
      linear := (-2921762114854645424610879448260000000000000)
      constant := (83183270618130753699647979974800054511339417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree093.table
  base := (5575790952574287920482821675421195203479/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1654374302599691484031430023956670000000000000)
      constant := (47269892953165701081107979303816092750704571510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237278940138179744651/50000000000000000000)
  centralHi := (474557880276359489303/100000000000000000000)
  directionLo := (119282507137081461687/25000000000000000000)
  directionHi := (477130028548325846749/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree094.table
  base := (115212417563876468313242728188368637369901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-823676586104041716370205429085720000000000000)
      constant := (23707088014475318783763689163022440344612273749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree094.table
  base := (23042483512775293657507397757168243129927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-3343273998949930588038825799788120000000000000)
      constant := (96572171026138937683376420391395721470052086315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119282507137081461687/25000000000000000000)
  centralHi := (477130028548325846749/100000000000000000000)
  directionLo := (479688384842348385427/100000000000000000000)
  directionHi := (119922096210587096357/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree095.table
  base := (11896453629498167695473548192994200859379/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-416090771081818679636987746053450000000000000)
      constant := (12105685315653192122052898244591409216163844855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree095.table
  base := (118964536294981676937769895635131322072057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-3377799392700478208014791551662900000000000000)
      constant := (98626252804299880166318118270915657201537761233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479688384842348385427/100000000000000000000)
  centralHi := (119922096210587096357/25000000000000000000)
  directionLo := (120558292166796748241/25000000000000000000)
  directionHi := (96446633733437398593/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree096.table
  base := (61386087620708624095745908203523643877501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (414549745043183852227786090655000000000000)
      linear := (-46704805456846277898763641951560000000000000)
      constant := (1373387797384578181632970905720866221766278461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree096.table
  base := (61386087620708624090146567316289563322027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (420189)
      previous := (0)
      next := (314160)
      square := (15084693063907488167069148599495000000000000)
      linear := (-1706162393225512913995378651768840000000000000)
      constant := (50351015620347944876480231744482049739807962163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120558292166796748241/25000000000000000000)
  centralHi := (96446633733437398593/20000000000000000000)
  directionLo := (48476459376993521277/10000000000000000000)
  directionHi := (484764593769935212771/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree097.table
  base := (63317667199940237399995273550300182848629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (103509)
      previous := (0)
      next := (78120)
      square := (3730947705388654670050074815895000000000000)
      linear := (-424595727141414322540757809074630000000000000)
      constant := (12617958589647411372425246939747601281457792221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree097.table
  base := (126635334399880474792597527533784285071679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-3446850180201573447966723055412460000000000000)
      constant := (102799506335211474074439532591512612664671542951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell212.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48476459376993521277/10000000000000000000)
  centralHi := (484764593769935212771/100000000000000000000)
  directionLo := (243641434172774172059/50000000000000000000)
  directionHi := (487282868345548344119/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree098.table
  base := (130554013767147390230170929485059057376563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (207018)
      previous := (0)
      next := (156240)
      square := (7461895410777309340100149631790000000000000)
      linear := (-857696410342424287985285681170440000000000000)
      constant := (25756181110395746583785373839340235787249893387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree098.table
  base := (130554013767147390225289675401022114038157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (840378)
      previous := (0)
      next := (628320)
      square := (30169386127814976334138297198990000000000000)
      linear := (-3481375573952121067942688807287240000000000000)
      constant := (104918678087733894244489587811107902305800312133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell212.Kernel098
