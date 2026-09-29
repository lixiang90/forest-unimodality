import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell138.Parameters
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch000_049
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch050_099
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch100_149
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch150_199
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch000_049
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch050_099
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch100_149
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree000.table
  base := (719331199711345278713281461/10000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (90442086241044987449111402500000000000)
      linear := (-6829550172141099755734883250000000000)
      constant := (89916399963918159839160182625000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree000.table
  base := (719331199711345278713281461/10000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (90442086241044987449111402500000000000)
      linear := (-6829550172141099755734883250000000000)
      constant := (89916399963918159839160182625000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree001.table
  base := (403825539551746764846380671324179765255401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-1930916745391833586335660750283428000000000000)
      constant := (953415525274256611442361796768485825183592519813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree001.table
  base := (100935587925408115883452022316393098114351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-482848456849188774661113703232903875000000000)
      constant := (238304875991160617004498008499083418112304356163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49922194835039704817/100000000000000000000)
  directionHi := (24961097417519852409/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree002.table
  base := (241654981215718553627645045765292760120921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-3732912727820976158127890660005398000000000000)
      constant := (572250290793997200801592269846058851587206763573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree002.table
  base := (48313958140739823541722803985814186847473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-3733866891830819182745478785301773000000000000)
      constant := (572050317420312779264852763565683080661131539745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922194835039704817/100000000000000000000)
  centralHi := (24961097417519852409/50000000000000000000)
  directionLo := (70600644999145227079/100000000000000000000)
  directionHi := (1765016124978630677/2500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree003.table
  base := (38754223332471356421272827424695240875533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-1383727177562529682480030142431842000000000000)
      constant := (92565861570221078427547514170158713345539048729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree003.table
  base := (3873726844421954639998878378490230706047/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-692042494533110408355812844708991312500000000)
      constant := (46263217338867660965815010698519702565016524055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70600644999145227079/100000000000000000000)
  centralHi := (1765016124978630677/2500000000000000000)
  directionLo := (8646777787964135569/10000000000000000000)
  directionHi := (86467777879641355691/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree004.table
  base := (21254766917769044819336982210471683861097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-7336904692679261301712350479449338000000000000)
      constant := (258645195943954050466882441753270948852673377305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree004.table
  base := (6638968762644764518694929369299140749347/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-917351627587368418868440841255261000000000000)
      constant := (32316315910401510412217752306722673770727845422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8646777787964135569/10000000000000000000)
  centralHi := (86467777879641355691/100000000000000000000)
  directionLo := (49922194835039704817/50000000000000000000)
  directionHi := (19968877934015881927/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree005.table
  base := (77070921707618459368107569424123070988049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-9138900675108403873504580389171308000000000000)
      constant := (194085118570486102927512584489993820653323265037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree005.table
  base := (38516910517330192448763369896597696954573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-4570643042566505717524275351206122750000000000)
      constant := (97001980327717118738044479374797192324383360249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922194835039704817/50000000000000000000)
  centralHi := (19968877934015881927/20000000000000000000)
  directionLo := (22325884247427536013/20000000000000000000)
  directionHi := (55814710618568840033/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree006.table
  base := (58341660019216504459616665426287878286401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-10940896657537546445296810298893278000000000000)
      constant := (155189795479823435876952283529329127347009522813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree006.table
  base := (7289214998168904004217571450522478311111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-1367969893695884439893696834347800375000000000)
      constant := (19391630131376401492595461790423812654178060043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22325884247427536013/20000000000000000000)
  centralHi := (55814710618568840033/50000000000000000000)
  directionLo := (122283904185653108721/100000000000000000000)
  directionHi := (61141952092826554361/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree007.table
  base := (22759453791761406059630152751044631585629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-6371446319983344508544520104307624000000000000)
      constant := (65591269588610911452190787730060646144660801577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree007.table
  base := (2843574572486537397449554757658068581013/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-1593279026750142450406324830894070062500000000)
      constant := (16392970790273045585625855779520113328002780938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122283904185653108721/100000000000000000000)
  centralHi := (61141952092826554361/50000000000000000000)
  directionLo := (660408562180141159/500000000000000000)
  directionHi := (132081712436028231801/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree008.table
  base := (905855643989109936233643557602926191189/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-1818111077799478948610158764792152250000000000)
      constant := (14559343881967384524550122954463217893850249285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree008.table
  base := (9054207880050642933443773991234739574901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-3637176319608800921837905654880679500000000000)
      constant := (29112491831785658842540110268753728552550873313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (660408562180141159/500000000000000000)
  centralHi := (132081712436028231801/100000000000000000000)
  directionLo := (70600644999145227079/50000000000000000000)
  directionHi := (141201289998290454159/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree009.table
  base := (5841740697672238051556494329826513785093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-16346884604824974160673500028059188000000000000)
      constant := (108048695954762055386841257208758149109923245045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree009.table
  base := (1167777555838142086519003474953228115137/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-16351178342869267771452646591892875500000000000)
      constant := (108035595765066290178373694591894459326694049525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70600644999145227079/50000000000000000000)
  centralHi := (141201289998290454159/100000000000000000000)
  directionLo := (149766584505119114451/100000000000000000000)
  directionHi := (37441646126279778613/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree010.table
  base := (741091824189259546125228335840290644381/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-2268610073406764591558216242222644750000000000)
      constant := (13023498215599463541051851163448066663039138212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree010.table
  base := (11851528553420298585625763993605886698677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-9076825703651665927776835282131516500000000000)
      constant := (52092655831753140542053562021835348536975332001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149766584505119114451/100000000000000000000)
  centralHi := (37441646126279778613/25000000000000000000)
  directionLo := (78933920736709654787/50000000000000000000)
  directionHi := (6314713658936772383/4000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree011.table
  base := (193135229427894684781329879794168100329/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-4987719142420814826064489961875782000000000000)
      constant := (25963947194555542707576981400811707280540316925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree011.table
  base := (19303539530319753938792130629188271213659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-19956124471737395939654694536633190500000000000)
      constant := (103862898943001803942344995510951597593900553967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78933920736709654787/50000000000000000000)
  centralHi := (6314713658936772383/4000000000000000000)
  directionLo := (82786594489422493071/50000000000000000000)
  directionHi := (165573188978844986143/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree012.table
  base := (1965251031670178347107874221251634586531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-2719109069014050234506273719653137250000000000)
      constant := (13298204365193931391651674866072306491628172503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree012.table
  base := (3142717358302050817605901862446635019379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-21758597536171460023755718509003348000000000000)
      constant := (106402240328692324239390397821357063739909701635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82786594489422493071/50000000000000000000)
  centralHi := (165573188978844986143/100000000000000000000)
  directionLo := (8646777787964135569/5000000000000000000)
  directionHi := (172935555759282711381/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree013.table
  base := (12748227658694384762825223185006511702243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-23554868534541544447842419666947068000000000000)
      constant := (111324085236172370705913898083175782847264711959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree013.table
  base := (12741118577319119116104198543720897274337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-23561070600605524107856742481373505500000000000)
      constant := (111350100616759579691175599025436354470815151581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8646777787964135569/5000000000000000000)
  centralHi := (172935555759282711381/100000000000000000000)
  directionLo := (179997033261439186271/100000000000000000000)
  directionHi := (5624907289419974571/3125000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree014.table
  base := (10255220655377948950652263256001090490553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-25356864516970687019634649576669038000000000000)
      constant := (118347965937751220745221165650442973135685235989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree014.table
  base := (5124613170868702626672534562431099574173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3205512)
      previous := (1602756)
      next := (1602756)
      square := (16106288486150255544887555002810000000000000)
      linear := (-239278713821128190490167608054185500000000000)
      constant := (1116824798322922343985996197557045265391756133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179997033261439186271/100000000000000000000)
  centralHi := (5624907289419974571/3125000000000000000)
  directionLo := (93395874534247107887/50000000000000000000)
  directionHi := (7471669962739768631/4000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree015.table
  base := (4070964982785460629376000167606570185411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-13579430249699914795713439743195504000000000000)
      constant := (63609410479874649161117694784796123769908205943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree015.table
  base := (2034221646778377543517566213317732669637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-6791504182368413069014697606528455125000000000)
      constant := (31815961996684675058725312452226851016706420481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93395874534247107887/50000000000000000000)
  centralHi := (7471669962739768631/4000000000000000000)
  directionLo := (193347829202230700159/100000000000000000000)
  directionHi := (302105983128485469/156250000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree016.table
  base := (6331969779819874611887189347859877575707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-28960856481828972163219109396112978000000000000)
      constant := (137756409353164774015674788277980177306046721391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree016.table
  base := (3163868868900673655679962482641980494757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-14484244896953858180079907199241989000000000000)
      constant := (68905587471845692872951542106444360521175049041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193347829202230700159/100000000000000000000)
  centralHi := (302105983128485469/156250000000000000)
  directionLo := (49922194835039704817/25000000000000000000)
  directionHi := (199688779340158819269/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree017.table
  base := (1191668348993685277361580837424744826511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-7690713116064528683752834826458737000000000000)
      constant := (37455575101234304914093435510095575601818100243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree017.table
  base := (595391520894338507937209102069053591131/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-3846370357292722555532604796356766937500000000)
      constant := (18735877973854285597274914438761099909532517303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922194835039704817/25000000000000000000)
  centralHi := (199688779340158819269/100000000000000000000)
  directionLo := (10291724118376656217/5000000000000000000)
  directionHi := (205834482367533124341/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree018.table
  base := (3400519810307590150055247697360485399407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-32564848446687257306803569215556918000000000000)
      constant := (163309082162897161734231977696292501034750949491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree018.table
  base := (3397564919619868035387317093085258204351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-32573435922775844528361862343224293000000000000)
      constant := (163384020443478407050703834425527214679843276163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10291724118376656217/5000000000000000000)
  centralHi := (205834482367533124341/100000000000000000000)
  directionLo := (211801934997435681237/100000000000000000000)
  directionHi := (105900967498717840619/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree019.table
  base := (439592186584046062794721983117026062123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-34366844429116399878595799125278888000000000000)
      constant := (178132874891995659098741702920506831837621191995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree019.table
  base := (1097750958001644664282139603146573417673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-17187954493604954306231443157797225250000000000)
      constant := (89109159113207825511103470641023498612108140549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211801934997435681237/100000000000000000000)
  centralHi := (105900967498717840619/50000000000000000000)
  directionLo := (217605802325686239107/100000000000000000000)
  directionHi := (54401450581421559777/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree020.table
  base := (1131126387445201013386652096252096274009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-36168840411545542450388029035000858000000000000)
      constant := (194227915289841158969907573361170607645403198517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree020.table
  base := (1129085199169300702696689206337168543743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-36178382051643972696563910287964608000000000000)
      constant := (194324183141835244070295431431698869029007051459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217605802325686239107/100000000000000000000)
  centralHi := (54401450581421559777/25000000000000000000)
  directionLo := (223258842474275360131/100000000000000000000)
  directionHi := (55814710618568840033/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree021.table
  base := (44528015366500640985461527405870158321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-9492709098493671255545064736180707000000000000)
      constant := (52885629532005556819508866765122146689386289773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree021.table
  base := (88210845651366556743818225509645340517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-18990427558039018390332467130167382750000000000)
      constant := (105824977999357250860424369331657001841185839921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223258842474275360131/100000000000000000000)
  centralHi := (55814710618568840033/25000000000000000000)
  directionLo := (11438611834495146093/5000000000000000000)
  directionHi := (228772236689902921861/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree022.table
  base := (-67832267019119422999286865084488812287/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-19886416188201913796986244427222399000000000000)
      constant := (115018001101625284696666215297235628500865175345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree022.table
  base := (-13594389363215314163831945111811047053/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-19891664090256050432382979116352461500000000000)
      constant := (115077489317232295511525620424219635652003237775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11438611834495146093/5000000000000000000)
  centralHi := (228772236689902921861/100000000000000000000)
  directionLo := (234155849419246047521/100000000000000000000)
  directionHi := (117077924709623023761/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree023.table
  base := (-1451760078999180232195110464551151608007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-41574828358832970165764718764166768000000000000)
      constant := (249676318611189458847347566762013131250775778709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree023.table
  base := (-1452911968219497826050395468727464625359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-41585801244946164948866982205075080500000000000)
      constant := (249807222396067161449447448328155702278587773933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234155849419246047521/100000000000000000000)
  centralHi := (117077924709623023761/50000000000000000000)
  directionLo := (239418435702842847203/100000000000000000000)
  directionHi := (59854608925710711801/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree024.table
  base := (-53822655712268702615816331144164549437/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55651250000000000000000000000000000000000000
      center := (801378)
      previous := (400689)
      next := (400689)
      square := (4026572121537563886221888750702500000000000)
      linear := (-102303830993542718720653180834643250000000000)
      constant := (637825955625349273935370543995138750472576615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree024.table
  base := (-1076927192852480225039743892598020486581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-21694137154690114516484003088722619000000000000)
      constant := (135290721391274556686939752833179208085597146847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239418435702842847203/100000000000000000000)
  centralHi := (59854608925710711801/25000000000000000000)
  directionLo := (122283904185653108721/50000000000000000000)
  directionHi := (244567808371306217443/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree025.table
  base := (-2790202850576481975489601412572770600339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-45178820323691255309349178583610708000000000000)
      constant := (292301742704767740150624183091985595795422291193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree025.table
  base := (-22327855759445568471502236171267271111/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-45190747373814293117069030149815395500000000000)
      constant := (292457735869971970887651637312672243592119994625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122283904185653108721/50000000000000000000)
  centralHi := (244567808371306217443/100000000000000000000)
  directionLo := (49922194835039704817/20000000000000000000)
  directionHi := (124805487087599262043/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree026.table
  base := (-1685153796046782822407381191163430998501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-23490408153060198940570704246666339000000000000)
      constant := (157625610850010987537722108729830542091334059887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree026.table
  base := (-337094679307455389791296889754893729949/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-23496610219124178600585027061092776500000000000)
      constant := (157710202671173971299771400903336642612219251315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922194835039704817/20000000000000000000)
  centralHi := (124805487087599262043/50000000000000000000)
  directionLo := (63638561406312097693/25000000000000000000)
  directionHi := (254554245625248390773/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree027.table
  base := (-194923585291099184064771986738014212791/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-12195703072137385113233409600763662000000000000)
      constant := (84818562811646214798745814823821120284067950585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree027.table
  base := (-1949497671886293348886423130734456954409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-24397846751341210642635539047277855250000000000)
      constant := (169728535758443523108673910531148560267748616283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63638561406312097693/25000000000000000000)
  centralHi := (254554245625248390773/100000000000000000000)
  directionLo := (259403333638924067071/100000000000000000000)
  directionHi := (1013294272027047137/390625000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree028.table
  base := (-2189418725003712090218962088945673699081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-25292404135489341512362934156388309000000000000)
      constant := (182180528609025254842569711731218289045890384347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree028.table
  base := (-4379265831364882484666440616861891215637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-50598166567116485369372102066925868000000000000)
      constant := (364557969821033688613421106305051395032997131519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259403333638924067071/100000000000000000000)
  centralHi := (1013294272027047137/390625000000000000)
  directionLo := (264163424872056463601/100000000000000000000)
  directionHi := (132081712436028231801/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree029.table
  base := (-1203668109828364504849737801611141721973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-13096701063351956399129524555624647000000000000)
      constant := (97625982327094943519438068462550994235490123551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree029.table
  base := (-2407511223213004268801857644041374874029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-26200319815775274726736563019648012750000000000)
      constant := (195357699014136821683418060472632558004680309223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264163424872056463601/100000000000000000000)
  centralHi := (132081712436028231801/50000000000000000000)
  directionLo := (268839246720567725283/100000000000000000000)
  directionHi := (67209811680141931321/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree030.table
  base := (-651069299598729478349693080343608654879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-6773600029479621021038791016527569750000000000)
      constant := (52212098136094257642846773725013706551034998173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree030.table
  base := (-1302210007248137453298116058954747366883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-13550778173996153384393537502916545750000000000)
      constant := (104480820128145916034594169612994642404512103721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268839246720567725283/100000000000000000000)
  centralHi := (67209811680141931321/25000000000000000000)
  directionLo := (27343512231319141459/10000000000000000000)
  directionHi := (273435122313191414591/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree031.table
  base := (-5562516844018548208859528188665065767797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-55990796218266110740102558041942528000000000000)
      constant := (445934826235212725279876836769534709918451217439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree031.table
  base := (-1112549936534017773266926902300357752843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-56005585760418677621675173984036340500000000000)
      constant := (446176824655491671458922930837323078724329351205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27343512231319141459/10000000000000000000)
  centralHi := (273435122313191414591/100000000000000000000)
  directionLo := (277955017316791053449/100000000000000000000)
  directionHi := (5559100346335821069/2000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree032.table
  base := (-293908200362612841139900905499423616991/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-14448198050173813327973696987916124500000000000)
      constant := (118803566848658761189524650461799266704205077585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree032.table
  base := (-2939176806409621652120202500361242354493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-28904029412426370852888098978203249000000000000)
      constant := (237736124936200041167236423135265905844187708791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277955017316791053449/100000000000000000000)
  centralHi := (5559100346335821069/2000000000000000000)
  directionLo := (70600644999145227079/25000000000000000000)
  directionHi := (282402579996580908317/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree033.table
  base := (-6156761453231300770778747928198079893523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-59594788183124395883687017861386468000000000000)
      constant := (505532122319288147807560892061279116858204513401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree033.table
  base := (-1231383140486687403391391526809592369519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-59610531889286805789877221928776655500000000000)
      constant := (505806573888567134839560523654874050366535819265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70600644999145227079/25000000000000000000)
  centralHi := (282402579996580908317/100000000000000000000)
  directionLo := (286781175682562791803/100000000000000000000)
  directionHi := (71695293920640697951/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree034.table
  base := (-6399307585367421328478292162205983009829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-61396784165553538455479247771108438000000000000)
      constant := (536886035163502445361540678381487135812228363823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree034.table
  base := (-1599858239004395766778686636569385256843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-15353251238430217468494561475286703250000000000)
      constant := (134294361039800494386933332304493391224069918241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286781175682562791803/100000000000000000000)
  centralHi := (71695293920640697951/25000000000000000000)
  directionLo := (29109391656821103917/10000000000000000000)
  directionHi := (291093916568211039171/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree035.table
  base := (-3303295022049550891900807140006857200077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-31599390073991340513635738840415204000000000000)
      constant := (284637073700329983276807333122099811536554709799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree035.table
  base := (-264267674188342069353171004485656147491/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-63215478018154933958079269873516970500000000000)
      constant := (569583004893189796569076692695273147661882975425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29109391656821103917/10000000000000000000)
  centralHi := (291093916568211039171/100000000000000000000)
  directionLo := (73835921897884617289/25000000000000000000)
  directionHi := (295343687591538469157/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree036.table
  base := (-1694807549942109867692655719183405086769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-16250194032602955899765926897638094500000000000)
      constant := (150673748209305921016789854460894437472993739603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree036.table
  base := (-6779312810327282176126586222197070734911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-65017951082588998042180293845887128000000000000)
      constant := (603021792158732550191743695943655695081984450557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73835921897884617289/25000000000000000000)
  centralHi := (295343687591538469157/100000000000000000000)
  directionLo := (299533169010238228903/100000000000000000000)
  directionHi := (37441646126279778613/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree037.table
  base := (-6917718252449048463298482367798848594203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-66802772112840966170855937500274348000000000000)
      constant := (637147414790727297176386469553828060222086876561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree037.table
  base := (-3458892616049300333951578143015501406003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-33410212073511531063140658909128642750000000000)
      constant := (318746325569730509208553326286433835001189543161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299533169010238228903/100000000000000000000)
  centralHi := (37441646126279778613/12500000000000000000)
  directionLo := (151832428086413414471/50000000000000000000)
  directionHi := (303664856172826828943/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree038.table
  base := (-87780511524382955002904748767442938717/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-8575596011908763592831020926249539750000000000)
      constant := (84078812594010057776309086695832232150451634790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree038.table
  base := (-7022495188579564847288420141634587115023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-68622897211457126210382341790627443000000000000)
      constant := (672994670862989076800486052456531701306259233901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151832428086413414471/50000000000000000000)
  centralHi := (303664856172826828943/100000000000000000000)
  directionLo := (15387053845003213387/5000000000000000000)
  directionHi := (307741076900064267741/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree039.table
  base := (-7093703292374417735266738301647454175747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-70406764077699251314440397319718288000000000000)
      constant := (709143530840871860228692831758767261460003094089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree039.table
  base := (-886718403565098814242585322853191889273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-8803171284486398786810420720374700062500000000)
      constant := (88690891589015704817875345505649149672279993651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15387053845003213387/5000000000000000000)
  centralHi := (307741076900064267741/100000000000000000000)
  directionLo := (38970500852559726211/12500000000000000000)
  directionHi := (311764006820477809689/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree040.table
  base := (-1426349209052782700093837848665364673063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-72208760060128393886232627229440258000000000000)
      constant := (746685937141802538938006683551152684338498976905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree040.table
  base := (-1782945398526509127126995471563127257039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-18056960835081313594646097433841939500000000000)
      constant := (186772367452072689473849686949193594603636434093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38970500852559726211/12500000000000000000)
  centralHi := (311764006820477809689/100000000000000000000)
  directionLo := (315735682946838619149/100000000000000000000)
  directionHi := (6314713658936772383/2000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree041.table
  base := (-1784189763711788390781505726930280041617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-18502689010639384114506214284790557000000000000)
      constant := (196314317906293918524794310977568900307659985779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree041.table
  base := (-7136787799524693930083498965215830044369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-74030316404759318462685413707737915500000000000)
      constant := (785681234971339463158169445816899933637141330803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315735682946838619149/100000000000000000000)
  centralHi := (6314713658936772383/2000000000000000000)
  directionLo := (319658015734087707233/100000000000000000000)
  directionHi := (159829007867043853617/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree042.table
  base := (-444305757083901885258027830886798252039/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-9476594003123334878727135881110524750000000000)
      constant := (103107147604915710562849811446796484382222998186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree042.table
  base := (-7108915342368029645792287251871874374869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-75832789469193382546786437680108073000000000000)
      constant := (825302075444811932345177309401359059703192234303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319658015734087707233/100000000000000000000)
  centralHi := (159829007867043853617/50000000000000000000)
  directionLo := (32353279982128848937/10000000000000000000)
  directionHi := (323532799821288489371/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree043.table
  base := (-7048263392172667923996332069593264529113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-77614748007415821601609316958606168000000000000)
      constant := (865485385945426808716271661161526756054666086731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree043.table
  base := (-3524141076635869867008241287911866125911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-38817631266813723315443730826239115250000000000)
      constant := (432975856479023539362911415939427260030353267557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32353279982128848937/10000000000000000000)
  centralHi := (323532799821288489371/100000000000000000000)
  directionLo := (81840430907249930211/25000000000000000000)
  directionHi := (65472344725799944169/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree044.table
  base := (-869370764629543497284072355371037551527/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-9927092998730620521675193358541017250000000000)
      constant := (113392708370863622071489371766877675219928720949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree044.table
  base := (-3477490630692818082709637840221593368691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-39718867799030755357494242812424194000000000000)
      constant := (453814963999126813513286764874923295781522923417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81840430907249930211/25000000000000000000)
  centralHi := (65472344725799944169/20000000000000000000)
  directionLo := (66229275591537994457/20000000000000000000)
  directionHi := (165573188978844986143/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree045.table
  base := (-1707268458471773219249810087713852236769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-20304684993068526686298444194512527000000000000)
      constant := (237456462590945980725889011897950211169540789603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree045.table
  base := (-3414543026203142345296757570505088340817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-40620104331247787399544754798609272750000000000)
      constant := (475168273701793973323487879904536625930172276179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66229275591537994457/20000000000000000000)
  centralHi := (165573188978844986143/50000000000000000000)
  directionLo := (334888263711413040197/100000000000000000000)
  directionHi := (167444131855706520099/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree046.table
  base := (-6670644563278243575841053728669015789051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-83020735954703249316986006687772078000000000000)
      constant := (993537799229999717198775944145558445646950002737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree046.table
  base := (-1334130883271671801040424080160408299169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-83042681726929638883190533569588703000000000000)
      constant := (994071434575995247213985253720224528272364692015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334888263711413040197/100000000000000000000)
  centralHi := (167444131855706520099/50000000000000000000)
  directionLo := (169294399426555594711/50000000000000000000)
  directionHi := (338588798853111189423/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree047.table
  base := (-3239862038868008462548992095356882629941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-42411365968566195944389118298747024000000000000)
      constant := (519138702780054227668393905988536589981917027167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree047.table
  base := (-6479732019558244771496095692147901008549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-84845154791363702967291557541958860500000000000)
      constant := (1038834481760641723005940932633641609373139668463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169294399426555594711/50000000000000000000)
  centralHi := (338588798853111189423/100000000000000000000)
  directionLo := (68449864936591439291/20000000000000000000)
  directionHi := (42781165585369649557/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree048.table
  base := (-782043560910967774523402468005949644529/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-10828090989945191807571308313402002250000000000)
      constant := (135505573018552527601684390730180880141423992723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree048.table
  base := (-625635488569180142730240244011136184791/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-43323813927898883525696290757164509000000000000)
      constant := (542312801977784956088586803310122941567983770585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68449864936591439291/20000000000000000000)
  centralHi := (42781165585369649557/12500000000000000000)
  directionLo := (345871111518565422761/100000000000000000000)
  directionHi := (172935555759282711381/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree049.table
  base := (-6000546279191860840450946738961710548453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-88426723901990677032362696416937988000000000000)
      constant := (1130839267776029660820511995378110362037633171311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree049.table
  base := (-3000275715944559266727421468287052552099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-44225050460115915567746802743349587750000000000)
      constant := (565722367053675116354387772476341770199196522313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345871111518565422761/100000000000000000000)
  centralHi := (172935555759282711381/50000000000000000000)
  directionLo := (8736384096131948343/2500000000000000000)
  directionHi := (349455363845277933721/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree050.table
  base := (-5712339927086263364344388989114829948321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-90228719884419819604154926326659958000000000000)
      constant := (1178661403413848651626290090558444438761152440227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree050.table
  base := (-2856172037437714128171187942077366700457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-45126286992332947609797314729534666500000000000)
      constant := (589645909660593204676458598809896296184084556859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8736384096131948343/2500000000000000000)
  centralHi := (349455363845277933721/100000000000000000000)
  directionLo := (88250806248931533849/25000000000000000000)
  directionHi := (353003224995726135397/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree051.table
  base := (-5391747160449608077400613040905240919467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-92030715866848962175947156236381928000000000000)
      constant := (1227510949227168867861077163629702773508293713729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree051.table
  base := (-168492203061811952990165559504060332483/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-11506880881137494912961956678929936312500000000)
      constant := (153520852233908696909092982043769062389333288684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88250806248931533849/25000000000000000000)
  centralHi := (353003224995726135397/100000000000000000000)
  directionLo := (11141118169068986933/3125000000000000000)
  directionHi := (356515781410207581857/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree052.table
  base := (-1259695491520660923489529309299736389587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-23458177962319526186934846536525974500000000000)
      constant := (319346968053138358612196701875395072618557450169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree052.table
  base := (-5038784650600248600984936785862478296787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-93857520113534023387796677403809648000000000000)
      constant := (1278069696842405966665296644574721579748683536569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11141118169068986933/3125000000000000000)
  centralHi := (356515781410207581857/100000000000000000000)
  directionLo := (359994066522878372543/100000000000000000000)
  directionHi := (5624907289419974571/1562500000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree053.table
  base := (-1163363844544848992284173611589985445261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1602756)
      previous := (801378)
      next := (801378)
      square := (8053144243075127772443777501405000000000000)
      linear := (-451107112413713430752507622904839000000000000)
      constant := (6265528992139503224977846897946122695491535019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree053.table
  base := (-4653457536653808896278019994443658413827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6411024)
      previous := (3205512)
      next := (3205512)
      square := (32212576972300511089775110005620000000000000)
      linear := (-1804905531659775235318824554267543500000000000)
      constant := (25075479816407976660909590333762516961883008133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359994066522878372543/100000000000000000000)
  centralHi := (5624907289419974571/1562500000000000000)
  directionLo := (363439064313161366531/100000000000000000000)
  directionHi := (90859766078290341633/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree054.table
  base := (-105894402540408326246692696272786389243/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-12179587976767048736415480745693479750000000000)
      constant := (172527968881261617245880276693186594948595785205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree054.table
  base := (-4235777836510223548719475031377317973007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-97462466242402151555998725348549963000000000000)
      constant := (1380958997670602386160777845747621959918259033709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363439064313161366531/100000000000000000000)
  centralHi := (90859766078290341633/25000000000000000000)
  directionLo := (366851712556959326163/100000000000000000000)
  directionHi := (91712928139239831541/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree055.table
  base := (-3785751003666749789447936165646453907681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-99238699796565532463116075875269808000000000000)
      constant := (1433182670158000856175330649130775757705535112547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree055.table
  base := (-757150479525130644363570253012582192271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-99264939306836215640099749320920120500000000000)
      constant := (1433945382887998262431301920048530121743369244385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366851712556959326163/100000000000000000000)
  centralHi := (91712928139239831541/25000000000000000000)
  directionLo := (185116452904058188907/50000000000000000000)
  directionHi := (74046581161623275563/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree056.table
  base := (-1651692750957729099344601070852111665099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-50520347889497337517454152892495889000000000000)
      constant := (743584445436947443648450565801571490237580753313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree056.table
  base := (-3303386621568413186676895450772532080991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-101067412371270279724200773293290278000000000000)
      constant := (1487959573176199574737985585399690031258776583517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185116452904058188907/50000000000000000000)
  centralHi := (74046581161623275563/20000000000000000000)
  directionLo := (93395874534247107887/25000000000000000000)
  directionHi := (373583498136988431549/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree057.table
  base := (-1394341935142812765595043693035201499133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-51421345880711908803350267847356874000000000000)
      constant := (771091201556485182439494075510595111460026284471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree057.table
  base := (-1394342384662158316307474856610424029607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-51434942717852171904150898632830217750000000000)
      constant := (771500779240464402731870910292588669782039437909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93395874534247107887/25000000000000000000)
  centralHi := (373583498136988431549/100000000000000000000)
  directionLo := (376904305649878327157/100000000000000000000)
  directionHi := (188452152824939163579/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree058.table
  base := (-224164948046407103132544131720899504887/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-52322343871926480089246382802217859000000000000)
      constant := (799111599459675619151957317912033692782875356345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree058.table
  base := (-448330040427143813329847182391351595089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-104672358500138407892402821238030593000000000000)
      constant := (1599071330870954796403591197681316290255786297215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376904305649878327157/100000000000000000000)
  centralHi := (188452152824939163579/50000000000000000000)
  directionLo := (38019610881039349331/10000000000000000000)
  directionHi := (380196108810393493311/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree059.table
  base := (-405831296963437199010689433330562173/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-13305835465785262843785624439269711000000000000)
      constant := (206911409002084485662491371896904439934781846912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree059.table
  base := (-332457114297306970492185673450941326891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-106474831564572471976503845210400750500000000000)
      constant := (1656168884089801633934104889906721139804778734085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38019610881039349331/10000000000000000000)
  centralHi := (380196108810393493311/100000000000000000000)
  directionLo := (191729827290716710909/50000000000000000000)
  directionHi := (383459654581433421819/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree060.table
  base := (-131324063046410507705643450531105064599/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-13531084963588905665259653177984957250000000000)
      constant := (214173327181694157085236926118558163835206359813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree060.table
  base := (-262648242242805592806544683849014598511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-27069326157251634015151217295692727000000000000)
      constant := (428573553300528960832775173630814712303663663757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191729827290716710909/50000000000000000000)
  centralHi := (383459654581433421819/100000000000000000000)
  directionLo := (386695658404461400319/100000000000000000000)
  directionHi := (302105983128485469/78125000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree061.table
  base := (-406573671898633709927800238083866601743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-110050675691140387893869455333601628000000000000)
      constant := (1772509231323862467887517412656269930026261394541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree061.table
  base := (-81314808903674375019095387957327993201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-110079777693440600144705893155141065500000000000)
      constant := (1773447314314704473963931037551292025500520043935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386695658404461400319/100000000000000000000)
  centralHi := (302105983128485469/78125000000000000)
  directionLo := (48738100753864713809/12500000000000000000)
  directionHi := (389904806030917710473/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree062.table
  base := (134885099559139461007358692122962408193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-55926335836784765232830842621661799000000000000)
      constant := (916329555273048286979887153986982707696883509309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree062.table
  base := (134884950174535781144508115021203466941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-55941125378937332114403458563755611500000000000)
      constant := (916814092178238532419271959521876361382489053833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48738100753864713809/12500000000000000000)
  centralHi := (389904806030917710473/100000000000000000000)
  directionLo := (393087755219054398859/100000000000000000000)
  directionHi := (19654387760952719943/5000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree063.table
  base := (244609519609711888180719449531649102043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-28413666913999668259363478788261392000000000000)
      constant := (473459063172321611797263133730547920070118989359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree063.table
  base := (122304729868231293940042038167663748797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-14210590477788591039113492637485172562500000000)
      constant := (236854602613106716904828250418705110563243260561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393087755219054398859/100000000000000000000)
  centralHi := (19654387760952719943/5000000000000000000)
  directionLo := (396245137308084695401/100000000000000000000)
  directionHi := (198122568654042347701/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree064.table
  base := (859714576659754707480613238546965643409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-57728331819213907804623072531383769000000000000)
      constant := (978020327917835905601733670469697457242741240717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree064.table
  base := (1719428961390612129130726577410356799157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-115487196886742792397008965072251538000000000000)
      constant := (1957073222048827917669758046658271456237929246241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396245137308084695401/100000000000000000000)
  centralHi := (198122568654042347701/50000000000000000000)
  directionLo := (399377558680317638537/100000000000000000000)
  directionHi := (199688779340158819269/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree065.table
  base := (2492742782599840523619746744799545547813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-117258659620856958181038374972489508000000000000)
      constant := (2019272318472362194482241324245846678818711676369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree065.table
  base := (498548525765241474896589977220232686639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-117289669951176856481109989044621695500000000000)
      constant := (2020337386280943976980100655882475229317716553535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399377558680317638537/100000000000000000000)
  centralHi := (199688779340158819269/50000000000000000000)
  directionLo := (402485602120868695963/100000000000000000000)
  directionHi := (100621400530217173991/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree066.table
  base := (3298378460481009382950196294720166245533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-119060655603286100752830604882211478000000000000)
      constant := (2083531239405868098843197487567924673635120858729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree066.table
  base := (3298378337306574310725893556902146517039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-119092143015610920565211013016991853000000000000)
      constant := (2084629312412084234502192846491009902962009945907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402485602120868695963/100000000000000000000)
  centralHi := (100621400530217173991/25000000000000000000)
  directionLo := (405569828083581543821/100000000000000000000)
  directionHi := (202784914041790771911/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree067.table
  base := (64630246686727409559365390791802301551/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-15107831448214405415577854348991681000000000000)
      constant := (268602177211834316538190451064502251002107278104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree067.table
  base := (165453427572363045364043305291861285199/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6411024)
      previous := (3205512)
      next := (3205512)
      square := (32212576972300511089775110005620000000000000)
      linear := (-2281030492076320465081359188478528500000000000)
      constant := (40565075462344322804520899473848008485083616975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405569828083581543821/100000000000000000000)
  centralHi := (202784914041790771911/50000000000000000000)
  directionLo := (25539423491934297069/6250000000000000000)
  directionHi := (81726155174189750621/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree068.table
  base := (5006614450239361523899308107980507632199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-122664647568144385896415064701655418000000000000)
      constant := (2215130852596048202688546381516122743555535978987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree068.table
  base := (5006614371262148081370810263430168083419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-122697089144479048733413060961732168000000000000)
      constant := (2216296446817531058746667517580533576951820556847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25539423491934297069/6250000000000000000)
  centralHi := (81726155174189750621/20000000000000000000)
  directionLo := (10291724118376656217/2500000000000000000)
  directionHi := (411668964735066248681/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree069.table
  base := (5909214199037461025775387699075979828159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-124466643550573528468207294611377388000000000000)
      constant := (2282471543524073676058169377415240550740261742467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree069.table
  base := (2954607067909049430730353248387830080543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-62249781104456556408757042467051162750000000000)
      constant := (1141835826884142628466483257790812324720152809859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10291724118376656217/2500000000000000000)
  centralHi := (411668964735066248681/100000000000000000000)
  directionLo := (82936978981197255483/20000000000000000000)
  directionHi := (51835611863248284677/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree070.table
  base := (3422067419232030107913511195243025247437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-63134319766501335519999762260549679000000000000)
      constant := (1175419745008274043988656648178754010533180561881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree070.table
  base := (6844134787869108633802677045713690854881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-126302035273347176901615108906472483000000000000)
      constant := (2352074619896132755101042263453284999531658321053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82936978981197255483/20000000000000000000)
  centralHi := (51835611863248284677/12500000000000000000)
  directionLo := (417679048553236087061/100000000000000000000)
  directionHi := (208839524276618043531/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree071.table
  base := (7811376213999305739252047675805884646179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-128070635515431813611791754430821328000000000000)
      constant := (2420234691708864383711893338545473722637624368727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree071.table
  base := (7811376173516032563908034061690717381041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-128104508337781240985716132878842640500000000000)
      constant := (2421505344837931130410552404995125656477255297133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417679048553236087061/100000000000000000000)
  centralHi := (208839524276618043531/50000000000000000000)
  directionLo := (42065189068573579111/10000000000000000000)
  directionHi := (420651890685735791111/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree072.table
  base := (2202734550938139034537437607637551663679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-32468157874465239045895996085135824500000000000)
      constant := (622664287078351955274877007145332895193788596227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree072.table
  base := (440546908568325640104447891334295382219/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-32476745350553826267454289212803199500000000000)
      constant := (622990957076810349294680378714712082648619606235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42065189068573579111/10000000000000000000)
  centralHi := (420651890685735791111/100000000000000000000)
  directionLo := (16944154799794854499/4000000000000000000)
  directionHi := (105900967498717840619/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree073.table
  base := (9842820711573932134689266555118447816451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-131674627480290098755376214250265268000000000000)
      constant := (2562106859603301895047757047734430798757519393463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree073.table
  base := (9842820685670555367634402977470921667727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-131709454466649369153918180823582955500000000000)
      constant := (2563450070078130624858742061161789708904775309651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16944154799794854499/4000000000000000000)
  centralHi := (105900967498717840619/25000000000000000000)
  directionLo := (42653541964505074801/10000000000000000000)
  directionHi := (426535419645050748011/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree074.table
  base := (2726755915405007782186424956515031454907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-33369155865679810331792111039996809500000000000)
      constant := (658645956349896381704287972313066678416407470991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree074.table
  base := (10907023640905582954950363620566139493329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-133511927531083433238019204795953113000000000000)
      constant := (2635964069972394758246829454875618664920772521677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42653541964505074801/10000000000000000000)
  centralHi := (426535419645050748011/100000000000000000000)
  directionLo := (4294469580156869717/1000000000000000000)
  directionHi := (429446958015686971701/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree075.table
  base := (12003546994066833553102621658166222930227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-135278619445148383898960674069709208000000000000)
      constant := (2708088045561097182124634294431608519537061722151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree075.table
  base := (12003546977504899980097702233615527149153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-135314400595517497322120228768323270500000000000)
      constant := (2709505827849479448076078315893796110253619357789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4294469580156869717/1000000000000000000)
  centralHi := (429446958015686971701/100000000000000000000)
  directionLo := (432338889398206778451/100000000000000000000)
  directionHi := (108084722349551694613/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree076.table
  base := (13132390661727629940515545827067635380959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-137080615427577526470752903979431178000000000000)
      constant := (2782619519976494487884071099399113962324170808867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree076.table
  base := (13132390648488132684067813644772800129689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-137116873659951561406221252740693428000000000000)
      constant := (2784075343598529193679873072340966317982415850357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432338889398206778451/100000000000000000000)
  centralHi := (108084722349551694613/25000000000000000000)
  directionLo := (87042320930274495643/20000000000000000000)
  directionHi := (54401450581421559777/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree077.table
  base := (14293554627384919393133875145519240061699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6411024)
      previous := (3205512)
      next := (3205512)
      square := (32212576972300511089775110005620000000000000)
      linear := (-2620426630377484321557455356399116000000000000)
      constant := (53927891482225632927346837037245207836786901179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree077.table
  base := (57174218467212750006603984032073498443/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-69459673362192812745161138356531792750000000000)
      constant := (1429836308566057696702264282007568739930510319875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87042320930274495643/20000000000000000000)
  centralHi := (54401450581421559777/12500000000000000000)
  directionLo := (2190327409089621717/500000000000000000)
  directionHi := (438065481817924343401/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree078.table
  base := (387175971542139007153058682641599505551/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-17585575924054476451792170474859389750000000000)
      constant := (366845528904528412418970709669528145670458558815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree078.table
  base := (3871759713307371652887364731120612875527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-35180454947204922393605825171358435750000000000)
      constant := (734074412095322197988849711954965308162185891051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2190327409089621717/500000000000000000)
  centralHi := (438065481817924343401/100000000000000000000)
  directionLo := (2755630541908111407/625000000000000000)
  directionHi := (440900886705297825121/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree079.table
  base := (16712843341480270582446652255789667415809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-142486603374864954186129593708597088000000000000)
      constant := (3012377467956677403655968403101750660250019321917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree079.table
  base := (1671284333472396360317429441758320129039/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-71262146426626876829262162328901950250000000000)
      constant := (1506975218645838335135097499418895697931023009535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2755630541908111407/625000000000000000)
  centralHi := (440900886705297825121/100000000000000000000)
  directionLo := (443718173432941028391/100000000000000000000)
  directionHi := (55464771679117628549/12500000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree080.table
  base := (8985484024256837641412931700561754957841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-72144299678647048378960911809159529000000000000)
      constant := (1545508979338116618946906137582750444301336075533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree080.table
  base := (1123185502694770473505805076289863157213/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-18040845739710977217828168578771757250000000000)
      constant := (386578872977550521715809312287998341997961677138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443718173432941028391/100000000000000000000)
  centralHi := (55464771679117628549/12500000000000000000)
  directionLo := (446517684948550720263/100000000000000000000)
  directionHi := (55814710618568840033/12500000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree081.table
  base := (19261412968390900098221724467451126620673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-146090595339723239329714053528041028000000000000)
      constant := (3170685703360928469559516866545508031988786079549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree081.table
  base := (9630706482039922584657126116072741319557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-73064619491060940913363186301272107750000000000)
      constant := (1586169643966832878019054683681586826996076351441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446517684948550720263/100000000000000000000)
  centralHi := (55814710618568840033/12500000000000000000)
  directionLo := (224649876757678671677/50000000000000000000)
  directionHi := (89859950703071468671/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree082.table
  base := (2573022261220291491187403972225149802823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-18486573915269047737688285429720374750000000000)
      constant := (406422587747997800504924116726317845651688587499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree082.table
  base := (20584178086319462775909872745758460024651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-147931712046555945910827396574914373000000000000)
      constant := (3253075349604809461878494145451302798446646820063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224649876757678671677/50000000000000000000)
  centralHi := (89859950703071468671/20000000000000000000)
  directionLo := (226032350586209522123/50000000000000000000)
  directionHi := (452064701172419044247/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree083.table
  base := (10969631701840245285763547417873495493271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-74847293652290762236649256673742484000000000000)
      constant := (1666551477262141225362085008599230056196363664123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree083.table
  base := (10969631700465687855230475009799741243639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-74867092555495004997464210273642265250000000000)
      constant := (1667419584406412878981226869385167470905439251707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226032350586209522123/50000000000000000000)
  centralHi := (452064701172419044247/100000000000000000000)
  directionLo := (454812840169729809463/100000000000000000000)
  directionHi := (56851605021216226183/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree084.table
  base := (4665333780618535671167481170430304456771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-151496583287010667045090743257206938000000000000)
      constant := (3415852460965186972510261551407211191950773948115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree084.table
  base := (23326668900897841686943540640931366995107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-151536658175424074079029444519654688000000000000)
      constant := (3417630745541155488361236332132311061419425413591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454812840169729809463/100000000000000000000)
  centralHi := (56851605021216226183/12500000000000000000)
  directionLo := (11438611834495146093/2500000000000000000)
  directionHi := (457544473379805843721/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree085.table
  base := (12373197291220372192450564025770404727463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-76649289634719904808441486583464454000000000000)
      constant := (1749814610646790442141948176691954756385183151819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree085.table
  base := (12373197290344340174237503800857295727631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-76669565619929069081565234246012422750000000000)
      constant := (1750725039888374783806198507889389998214075066803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11438611834495146093/2500000000000000000)
  centralHi := (457544473379805843721/100000000000000000000)
  directionLo := (115064973671821479319/25000000000000000000)
  directionHi := (460259894687285917277/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree086.table
  base := (26198440437345350839949054862400173376249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-155100575251868952188675203076650878000000000000)
      constant := (3584433235499130643596514959302723608300851031637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree086.table
  base := (2619844043594693083147207909174819071283/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-77570802152146101123615746232197501500000000000)
      constant := (1793148585754663627110866737481929008422486467395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115064973671821479319/25000000000000000000)
  centralHi := (460259894687285917277/100000000000000000000)
  directionLo := (92591877871592859993/20000000000000000000)
  directionHi := (231479694678982149983/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree087.table
  base := (27682806464356902353422132102271805807867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-156902571234298094760467432986372848000000000000)
      constant := (3670264503573696540374085246647021662267718475471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree087.table
  base := (1384140323162044813858496559430418655507/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-39236019342181566582833129109191290125000000000)
      constant := (918043005182697767917311266804370738091290443955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92591877871592859993/20000000000000000000)
  centralHi := (231479694678982149983/50000000000000000000)
  directionLo := (465643234388567975143/100000000000000000000)
  directionHi := (58205404298570996893/12500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree088.table
  base := (29199492660759065265847239536044447935841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-158704567216727237332259662896094818000000000000)
      constant := (3757123025510869078401376867759472091927233589533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree088.table
  base := (5839898531973711337455404178387044888663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-158746550433160330415433540409135318000000000000)
      constant := (3759074627434765298440703089885946544754363837095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465643234388567975143/100000000000000000000)
  centralHi := (58205404298570996893/12500000000000000000)
  directionLo := (234155849419246047521/50000000000000000000)
  directionHi := (468311698838492095043/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree089.table
  base := (30748499024413774454311844327944549143917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-160506563199156379904051892805816788000000000000)
      constant := (3845008801305603251419518812297856762189125424121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree089.table
  base := (3843562377962911456296969313013883765969/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-20068627937199299312441820547688184437500000000)
      constant := (480875623952028991670907655056454007504122534997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234155849419246047521/50000000000000000000)
  centralHi := (468311698838492095043/100000000000000000000)
  directionLo := (470965044144618214213/100000000000000000000)
  directionHi := (235482522072309107107/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree090.table
  base := (6465965110727793828077673531220266179729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-162308559181585522475844122715538758000000000000)
      constant := (3933921830953930046948943245715564699705744424385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree090.table
  base := (16164912776536094775019999804025772986101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-81175748281014229291817794176937816500000000000)
      constant := (1967981556635621776225474701661732905179302738913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470965044144618214213/100000000000000000000)
  centralHi := (235482522072309107107/50000000000000000000)
  directionLo := (473603524420257928723/100000000000000000000)
  directionHi := (118400881105064482181/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree091.table
  base := (33943472247112148048715653169728569008757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-164110555164014665047636352625260728000000000000)
      constant := (4023862114452728873787791403792248169654460131041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree091.table
  base := (16971736123330030942638107068222352888043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-82076984813231261333868306163122895250000000000)
      constant := (2012974496198348409903686351861685826210526307359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473603524420257928723/100000000000000000000)
  centralHi := (118400881105064482181/25000000000000000000)
  directionLo := (119056846684797361873/25000000000000000000)
  directionHi := (476227386739189447493/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree092.table
  base := (7117887820758858587156546381856916577123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-165912551146443807619428582534982698000000000000)
      constant := (4114829651799548050981437638528376148476474666995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree092.table
  base := (35589439103433734401362347987913401214911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-165956442690896586751837636298615948000000000000)
      constant := (4116962628990153844033823680845488749130919789443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119056846684797361873/25000000000000000000)
  centralHi := (476227386739189447493/100000000000000000000)
  directionLo := (239418435702842847203/50000000000000000000)
  directionHi := (478836871405685694407/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree093.table
  base := (37267726122869860236559962874126196511907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-167714547128872950191220812444704668000000000000)
      constant := (4206824442992463211331771663633497989680050411991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree093.table
  base := (18633863061291166486641367468446919416911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-83879457877665325417969330135493052750000000000)
      constant := (2104502011524850638001775871730157920561408115443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239418435702842847203/50000000000000000000)
  centralHi := (478836871405685694407/100000000000000000000)
  directionLo := (481432212211369216751/100000000000000000000)
  directionHi := (30089513263210576047/6250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree094.table
  base := (38978333303699448385919226174658173382901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-169516543111302092763013042354426638000000000000)
      constant := (4299846488029965614593496820750566208470547177313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree094.table
  base := (7795666660694037278353850750067904279607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-169561388819764714920039684243356263000000000000)
      constant := (4302073174573839177667442112220780383917081560455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481432212211369216751/100000000000000000000)
  centralHi := (30089513263210576047/6250000000000000000)
  directionLo := (484013636679670945987/100000000000000000000)
  directionHi := (121003409169917736497/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree095.table
  base := (4072126064578246454205773616084736956809/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-85659269546865617667402636132074304000000000000)
      constant := (2196947893455437027694694156711774573999334774585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree095.table
  base := (2545078790349980092529652132604154806509/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-21420482735524847375517588526965802562500000000)
      constant := (549521260445174171813201750459294106447855367034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484013636679670945987/100000000000000000000)
  centralHi := (121003409169917736497/25000000000000000000)
  directionLo := (486581366298616261699/100000000000000000000)
  directionHi := (4865813662986162617/1000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree096.table
  base := (849930162974553588502411911975427941749/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-86560267538080188953298751086935289000000000000)
      constant := (2244486169817132692012359944012809750297854578425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree096.table
  base := (1062412703714549215940044537208988265801/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-21645791868579105386030216523512072250000000000)
      constant := (561411843751430791492827948237111640644157475065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486581366298616261699/100000000000000000000)
  centralHi := (4865813662986162617/1000000000000000000)
  directionLo := (122283904185653108721/25000000000000000000)
  directionHi := (97827123348522486977/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree097.table
  base := (8860815162446000940145873035624369456473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-174922531058589520478389732083592548000000000000)
      constant := (4585076146199419710099543832240462511181483124745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree097.table
  base := (22152037906056929874598459023528369579019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-87484404006533453586171378080233367750000000000)
      constant := (2293723586961641321681669313808338459610270259647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122283904185653108721/25000000000000000000)
  centralHi := (97827123348522486977/20000000000000000000)
  directionLo := (491676598083865999961/100000000000000000000)
  directionHi := (245838299041932999981/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree098.table
  base := (11535990909013044740709423192237323027573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-44181131760254665762545490498328629500000000000)
      constant := (1170551801651444297128938723744917955001060609249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree098.table
  base := (922879272719192211035449245745812862401/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-88385640538750485628221890066418446500000000000)
      constant := (2342313677648173021769479439042822790298465270325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491676598083865999961/100000000000000000000)
  centralHi := (245838299041932999981/50000000000000000000)
  directionLo := (247102257497008294777/50000000000000000000)
  directionHi := (98840902998803317911/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree099.table
  base := (9603234324002065153192697535376752796139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-178526523023447805621974191903036488000000000000)
      constant := (4780365520852903942022199743773633024727779671035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree099.table
  base := (24008085809968277859592570854519050467757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-89286877070967517670272402052603525250000000000)
      constant := (2391417647065102756495633715825101002051687998041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247102257497008294777/50000000000000000000)
  centralHi := (98840902998803317911/20000000000000000000)
  directionLo := (124179891734133739607/25000000000000000000)
  directionHi := (496719566936534958429/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree100.table
  base := (49920699763962565993121150228685681658709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-180328519005876948193766421812758458000000000000)
      constant := (4879551088940465190810010636820574257355751319617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree100.table
  base := (12480174940975945706028230526329071030939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-45094056801592274856161457019394302000000000000)
      constant := (1220517747606132138231223415302276204220027066607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124179891734133739607/25000000000000000000)
  centralHi := (496719566936534958429/100000000000000000000)
  directionLo := (499221948350397048171/100000000000000000000)
  directionHi := (124805487087599262043/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree101.table
  base := (51857548067800039484574571551970318374521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-182130514988306090765558651722480428000000000000)
      constant := (4979763910868204067031092175055801175600658620373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree101.table
  base := (12964387016938300798271625364575834783051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-45544675067700790877186713012486841375000000000)
      constant := (1245583611044765028975191661655043835400095569263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499221948350397048171/100000000000000000000)
  centralHi := (124805487087599262043/25000000000000000000)
  directionLo := (15678495275797273551/3125000000000000000)
  directionHi := (501711848825512753633/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree102.table
  base := (53826716531439827046156637247610392049249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-183932510970735233337350881632202398000000000000)
      constant := (5081003986635924913476938111170645856014504580637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree102.table
  base := (53826716531402513250442770598613831962377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-183981173335237227592847876022317523000000000000)
      constant := (5083625655393605997331805231866912506190740280101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15678495275797273551/3125000000000000000)
  centralHi := (501711848825512753633/100000000000000000000)
  directionLo := (12604736331758933009/2500000000000000000)
  directionHi := (504189453270357320361/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree103.table
  base := (27914102577409685698980302210870786261183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-92867253476582187954571555770962184000000000000)
      constant := (2591635658121740059588317927922544202457108802179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree103.table
  base := (55828205154789646894129558183809891585921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-185783646399671291676948899994687680500000000000)
      constant := (5185944624068019745236747786771472458480354808573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12604736331758933009/2500000000000000000)
  centralHi := (504189453270357320361/100000000000000000000)
  directionLo := (25332747103611241247/5000000000000000000)
  directionHi := (506654942072224824941/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree104.table
  base := (57862013937892080384198691060733689856749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-187536502935593518480935341451646338000000000000)
      constant := (5286565899690759744673690533398600896123953078137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree104.table
  base := (57862013937868403810192404559878347740557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-187586119464105355761049923967057838000000000000)
      constant := (5289291350202192344754183286926270219747138924441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25332747103611241247/5000000000000000000)
  centralHi := (506654942072224824941/100000000000000000000)
  directionLo := (101821698250099356309/20000000000000000000)
  directionHi := (254554245625248390773/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree105.table
  base := (59928142880623862631174696392871805899673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-189338498918022661052727571361368308000000000000)
      constant := (5390887736977683347519540730439634729284345106549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree105.table
  base := (11985628576121001036346940007010155792181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-189388592528539419845150947939427995500000000000)
      constant := (5393665833796044090948637872446683029711902929765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101821698250099356309/20000000000000000000)
  centralHi := (254554245625248390773/50000000000000000000)
  directionLo := (127887568150823602383/25000000000000000000)
  directionHi := (511550272603294409533/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree106.table
  base := (62026591982990398590069555282588423954969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6411024)
      previous := (3205512)
      next := (3205512)
      square := (32212576972300511089775110005620000000000000)
      linear := (-3606424432083996294802260401341326000000000000)
      constant := (103702581662343274396049789551442605222899174849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree106.table
  base := (31013295991487690371970998609323422972333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3205512)
      previous := (1602756)
      next := (1602756)
      square := (16106288486150255544887555002810000000000000)
      linear := (-1803689298046919659709924263318850500000000000)
      constant := (51878000706127530068965489912092881895401237493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127887568150823602383/25000000000000000000)
  centralHi := (511550272603294409533/100000000000000000000)
  directionLo := (513980453847860335079/100000000000000000000)
  directionHi := (12849511346196508377/2500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree107.table
  base := (64157361244974991514614792341030596473797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-192942490882880946196312031180812248000000000000)
      constant := (5602613173070250933227432084741353468587325560561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree107.table
  base := (32078680622481516273429533979291184173327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-96496769328703774006676497942084155250000000000)
      constant := (2802749036681287852531053877933066882156089142451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513980453847860335079/100000000000000000000)
  centralHi := (12849511346196508377/2500000000000000000)
  directionLo := (516399198754994344839/100000000000000000000)
  directionHi := (12909979968874858621/2500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree108.table
  base := (8290056333320859468958704359254441080899/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-24343060858163761096013032636316777250000000000)
      constant := (713752096484478764431851998488141168732223332087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree108.table
  base := (66320450666557353452867473626931557074053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-194796011721841612097454019856538468000000000000)
      constant := (5712955829335191615464118091173392024932177421489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516399198754994344839/100000000000000000000)
  centralHi := (12909979968874858621/2500000000000000000)
  directionLo := (259403333638924067071/50000000000000000000)
  directionHi := (518806667277848134143/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree109.table
  base := (34257930123879942809939778651416480209001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-98273241423869615669948245500128094000000000000)
      constant := (2909223812260458270525456279776643445490401476613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree109.table
  base := (34257930123876152081403731445639673650993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-98299242393137838090777521914454312750000000000)
      constant := (2910720671383675834053782349141443177207953045709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259403333638924067071/50000000000000000000)
  centralHi := (518806667277848134143/100000000000000000000)
  directionLo := (260601507837682840061/50000000000000000000)
  directionHi := (521203015675365680123/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree110.table
  base := (35371794994275704290557204730565287442227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-99174239415084186955844360454989079000000000000)
      constant := (2963952865502752022718393450830745289597415578151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree110.table
  base := (70743589988545372890079658008409302334463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-198400957850709740265656067801278783000000000000)
      constant := (5930954613659049936148134459679812586921829242819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260601507837682840061/50000000000000000000)
  centralHi := (521203015675365680123/100000000000000000000)
  directionLo := (523588396630638815239/100000000000000000000)
  directionHi := (13089709915765970381/2500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree111.table
  base := (36501819944470781262765042647479591600079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-100075237406298758241740475409850064000000000000)
      constant := (3019195545664796453393791716805708007449237209427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree111.table
  base := (9125454986117094729365507784132116664969/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-25025428864392975543719636471706117562500000000)
      constant := (755186955251285860907711286282308933264630621997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523588396630638815239/100000000000000000000)
  centralHi := (13089709915765970381/2500000000000000000)
  directionLo := (525962959364431682059/100000000000000000000)
  directionHi := (26298147968221584103/5000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree112.table
  base := (37648004974466274852234030384688512289721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-100976235397513329527636590364711049000000000000)
      constant := (3074951852746594160782098384764701082549485437973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree112.table
  base := (37648004974464362628922584968660568716459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-101002951989788934216929057873009549000000000000)
      constant := (3076532213910533934472989990607270413530749970367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525962959364431682059/100000000000000000000)
  centralHi := (26298147968221584103/5000000000000000000)
  directionLo := (264163424872056463601/50000000000000000000)
  directionHi := (528326849744112927203/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree113.table
  base := (77620700168528149874371413164582131049879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-203754466777455801627065410639144068000000000000)
      constant := (6262443573496299208529066828325808948742998136827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree113.table
  base := (31048280067410042370747568912137445629/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-50952094261002983129489784929597313875000000000)
      constant := (1566415242772850480082759381981880013124519735625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264163424872056463601/50000000000000000000)
  centralHi := (528326849744112927203/100000000000000000000)
  directionLo := (530680210388220659897/100000000000000000000)
  directionHi := (265340105194110329949/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree114.table
  base := (19994427636933330781543323505702309919301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-51389115689971236049714410137216509500000000000)
      constant := (1594002673834734317894310164127665875115611590513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree114.table
  base := (79977710547730900582029870393077497504719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-205610850108445996602060163690759413000000000000)
      constant := (6379285271821300841228058077600786340432102513747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530680210388220659897/100000000000000000000)
  centralHi := (265340105194110329949/50000000000000000000)
  directionLo := (266511590383436142113/50000000000000000000)
  directionHi := (533023180766872284227/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree115.table
  base := (41183520543276949557643292423718004580781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-103679229371157043385324935229294004000000000000)
      constant := (3245302535510558133219708004823397643817870397753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree115.table
  base := (4118352054327598563357010597669293213341/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-51853330793220015171540296915782392625000000000)
      constant := (1623484332502694615947956865358398804620212235165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266511590383436142113/50000000000000000000)
  centralHi := (533023180766872284227/100000000000000000000)
  directionLo := (535355897298219245789/100000000000000000000)
  directionHi := (53535589729821924579/10000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree116.table
  base := (84788691784996334330092460360332084611567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-209160454724743229342442100368309978000000000000)
      constant := (6606226700542851427929511456563199309166553443571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree116.table
  base := (2119717294624870006861905722284774008429/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-26151974529664265596282776454437466000000000000)
      constant := (826202143207481260465433824232491028730505889885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535355897298219245789/100000000000000000000)
  centralHi := (53535589729821924579/10000000000000000000)
  directionLo := (268839246720567725283/50000000000000000000)
  directionHi := (537678493441135450567/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree117.table
  base := (10905332830383440364991772218075530764409/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-26370306338396546489279291284753993500000000000)
      constant := (840359447988019877946492661046434712967349413717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree117.table
  base := (87242662643066302309406010399753487094601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-211018269301748188854363235607869885500000000000)
      constant := (6726324718768532017051665187923947070084377749413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268839246720567725283/50000000000000000000)
  centralHi := (537678493441135450567/100000000000000000000)
  directionLo := (107998219956863511763/20000000000000000000)
  directionHi := (16874721868259923713/3125000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree118.table
  base := (44864476830387324833287268854127678654113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-106382223344800757243013280093876959000000000000)
      constant := (3420275860552528003335577586269321616212067538269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree118.table
  base := (17945790732154735705516665402215793985583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-212820742366182252938464259580240043000000000000)
      constant := (6844060049336841255716906904073404660781017296895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107998219956863511763/20000000000000000000)
  centralHi := (16874721868259923713/3125000000000000000)
  directionLo := (21691753765278619083/4000000000000000000)
  directionHi := (135573461032991369269/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree119.table
  base := (92247564838125076099035634997317729518003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-214566442672030657057818790097475888000000000000)
      constant := (6959255112145559747586733521114665435451163612839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree119.table
  base := (115309456047655379374292426973797852151/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-26827901928827039627820660444076275062500000000)
      constant := (870352892170599400106430223484092486413960881300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21691753765278619083/4000000000000000000)
  centralHi := (135573461032991369269/25000000000000000000)
  directionLo := (6807335644827526479/1250000000000000000)
  directionHi := (544586851586202118321/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree120.table
  base := (94798496175126252657315179151325985421371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-216368438654459799629611020007197858000000000000)
      constant := (7078985757025687826473750649499254222438077489423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree120.table
  base := (94798496175125638051168691343489123891353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6411024)
      previous := (3205512)
      next := (3205512)
      square := (32212576972300511089775110005620000000000000)
      linear := (-4083503556510384549182383160848686000000000000)
      constant := (133634226091554933153165805124792549284766926913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6807335644827526479/1250000000000000000)
  centralHi := (544586851586202118321/100000000000000000000)
  directionLo := (546870244626382829181/100000000000000000000)
  directionHi := (273435122313191414591/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree121.table
  base := (97381747671785651313432520179021565432777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-218170434636888942201403249916919828000000000000)
      constant := (7199743655745457874294519052224586009825531235301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree121.table
  base := (97381747671785162425679230421575762610193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-218228161559484445190767331497350515500000000000)
      constant := (7203432585799707674994314859943517456455550335309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546870244626382829181/100000000000000000000)
  centralHi := (273435122313191414591/50000000000000000000)
  directionLo := (549144143185436752989/100000000000000000000)
  directionHi := (54914414318543675299/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree122.table
  base := (99997319328110714243615692619022138145857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-219972430619318084773195479826641798000000000000)
      constant := (7321528808304887451704814690552432050456760073341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree122.table
  base := (19999463865622065076995018509357504294281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-220030634623918509274868355469720673000000000000)
      constant := (7325278946206701430676694954782756867714206366265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549144143185436752989/100000000000000000000)
  centralHi := (54914414318543675299/10000000000000000000)
  directionLo := (55140866472337477009/10000000000000000000)
  directionHi := (551408664723374770091/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree123.table
  base := (5132260557205440754013292145339560229937/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-55443606650436806836246927434090942000000000000)
      constant := (1861085303675998489405877132706703920601711671905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree123.table
  base := (51322605572054252902506887957691305118887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-110916553844176286679484689721045415250000000000)
      constant := (3724076532036705067728281328161545384490804810731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55140866472337477009/10000000000000000000)
  centralHi := (551408664723374770091/100000000000000000000)
  directionLo := (553663924298091497567/100000000000000000000)
  directionHi := (17301997634315359299/3125000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree124.table
  base := (10532542311978723000953534103388952927583/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-111788211292088184958389969823042869000000000000)
      constant := (3784090437471397280517018062630316787921564526895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree124.table
  base := (105325423119786984046480333482380889690689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-223635580752786637443070403414460988000000000000)
      constant := (7572054939399850968167635104422872439015715743357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553663924298091497567/100000000000000000000)
  centralHi := (17301997634315359299/3125000000000000000)
  directionLo := (555910034633582106899/100000000000000000000)
  directionHi := (5559100346335821069/1000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree125.table
  base := (54018977627576558280834183801898891028997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-112689209283302756244286084777903854000000000000)
      constant := (3846523894510653075468904767790103282332604698161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree125.table
  base := (1080379552551529209627981453466746695833/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-56359513454305175381792856846707786375000000000)
      constant := (1924246143046510206413185300316847364377521065725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555910034633582106899/100000000000000000000)
  centralHi := (5559100346335821069/1000000000000000000)
  directionLo := (558147106185688400329/100000000000000000000)
  directionHi := (55814710618568840033/10000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree126.table
  base := (55391403775106749199801648511727843429637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-113590207274517327530182199732764839000000000000)
      constant := (3909470978469772650230602884117508455818536050481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree126.table
  base := (55391403775106671431070331737645223841671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-113620263440827382805636225679600651500000000000)
      constant := (3911470981215998143639994515186456559970966833323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558147106185688400329/100000000000000000000)
  centralHi := (55814710618568840033/10000000000000000000)
  directionLo := (560375247205482647323/100000000000000000000)
  directionHi := (140093811801370661831/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree127.table
  base := (2271199600099505095453968360545016357777/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-114491205265731898816078314687625824000000000000)
      constant := (3972931689348764120985220441490239541950581507525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree127.table
  base := (113559980004975131099292422664645349282117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-229042999946088829695373475331571460500000000000)
      constant := (7949927110137733590383585792244021628571248940721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560375247205482647323/100000000000000000000)
  centralHi := (140093811801370661831/25000000000000000000)
  directionLo := (562594563800392095931/100000000000000000000)
  directionHi := (140648640950098023983/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree128.table
  base := (116369472619445113587305887020972000985189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-230784406513892940203948859284973618000000000000)
      constant := (8073812054295270850720806210649725670160664771857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree128.table
  base := (116369472619445015256249181255083748670421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-230845473010522893779474499303941618000000000000)
      constant := (8077940015303268614172693244205449993451458107073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562594563800392095931/100000000000000000000)
  centralHi := (140648640950098023983/25000000000000000000)
  directionLo := (564805159993161816633/100000000000000000000)
  directionHi := (282402579996580908317/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree129.table
  base := (59605642696814823635223166061407394334101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-116293201248161041387870544597347794000000000000)
      constant := (4101393991866394317548270588309308216341871062913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree129.table
  base := (119211285393629569093521467986541380239293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-232647946074956957863575523276311775500000000000)
      constant := (8206980677928616870178070916508824192616203873609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564805159993161816633/100000000000000000000)
  centralHi := (282402579996580908317/50000000000000000000)
  directionLo := (567007137778748586433/100000000000000000000)
  directionHi := (283503568889374293217/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree130.table
  base := (61042709163767635389889115071888077201069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3205512)
      previous := (1602756)
      next := (1602756)
      square := (16106288486150255544887555002810000000000000)
      linear := (-2211211306403313446674842633060543000000000000)
      constant := (78611237424623554074671048795571494085068792949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree130.table
  base := (122085418327535208629888612107053738491797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-234450419139391021947676547248681933000000000000)
      constant := (8337049098013793497721038758579089003356344594561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567007137778748586433/100000000000000000000)
  centralHi := (283503568889374293217/50000000000000000000)
  directionLo := (569200597179233858417/100000000000000000000)
  directionHi := (284600298589616929209/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree131.table
  base := (62495935710584120626234809020529181695121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-118095197230590183959662774507069764000000000000)
      constant := (4231910802063604952799390340487153199882169548173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree131.table
  base := (124991871421168191846839617506556597286679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-236252892203825086031777571221052090500000000000)
      constant := (8468145275558813263216071983351987446834037495227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569200597179233858417/100000000000000000000)
  centralHi := (284600298589616929209/50000000000000000000)
  directionLo := (114277127259367893587/20000000000000000000)
  directionHi := (17855801134276233373/3125000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree132.table
  base := (31982661168633664723849604633617808140253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-59498097610902377622779444730965374500000000000)
      constant := (2148969823771035637568735384603114778619246802089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree132.table
  base := (12793064467453461962301908653877251663133/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-119027682634129575057939297596711124000000000000)
      constant := (4300134605281845281187865908460596937018001237645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114277127259367893587/20000000000000000000)
  centralHi := (17855801134276233373/3125000000000000000)
  directionLo := (573562351365125583607/100000000000000000000)
  directionHi := (71695293920640697951/12500000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree133.table
  base := (32725434521910117201397407760630432387981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-59948596606509663265727502208395867000000000000)
      constant := (2182241059970227173517960048649484499645801011353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree133.table
  base := (65450869043820218794945446439395629175633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-119928919166346607099989809582896202750000000000)
      constant := (4366710451514219712294656812320403931566315410029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573562351365125583607/100000000000000000000)
  centralHi := (71695293920640697951/12500000000000000000)
  directionLo := (287865418399223251681/50000000000000000000)
  directionHi := (575730836798446503363/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree134.table
  base := (836907197878071646736744015947212704197/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-30199547801058474454337779842913179750000000000)
      constant := (1107884554814690250629449200671118949711767915220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree134.table
  base := (33476287915122859666861346724293939575587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-60415077849281819571020160784540640750000000000)
      constant := (2216900088238268379726533649279941133721894567831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287865418399223251681/50000000000000000000)
  centralHi := (575730836798446503363/100000000000000000000)
  directionLo := (18059099538741756491/3125000000000000000)
  directionHi := (577891185239736207713/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree135.table
  base := (136940885393093285810367417492467824171497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-243398378390896938206494468653027408000000000000)
      constant := (8998215890993995798221918009786588403746778550661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree135.table
  base := (136940885393093266091976932066417525519173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-243462784461561342368181667110532720500000000000)
      constant := (9002807560337606161179916986234479996408497360049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18059099538741756491/3125000000000000000)
  centralHi := (577891185239736207713/100000000000000000000)
  directionLo := (580043487606692100479/100000000000000000000)
  directionHi := (906317949385456407/156250000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree136.table
  base := (70004469642725716230183628584437165533503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-122600187186663040389143349281374689000000000000)
      constant := (4567191298655171521807432265494683207476005614339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree136.table
  base := (140008939285451416789799191238389624065759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-245265257525995406452282691082902878000000000000)
      constant := (9139042525182050322029450552927851004010677791267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580043487606692100479/100000000000000000000)
  centralHi := (906317949385456407/156250000000000000)
  directionLo := (29109391656821103917/5000000000000000000)
  directionHi := (582187833136422078341/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree137.table
  base := (143109313337571257436668246288612952740587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-247002370355755223350078928472471348000000000000)
      constant := (9271576557466576374603175423279804680005074712831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree137.table
  base := (17888664167196405622956564663757500430621/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-30883466323803683817047964381909129437500000000)
      constant := (1159538155935802329418539791190018848990552034673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29109391656821103917/5000000000000000000)
  centralHi := (582187833136422078341/100000000000000000000)
  directionLo := (146081077357154240681/25000000000000000000)
  directionHi := (23372972377144678509/4000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree138.table
  base := (73121003774728987919983828107423826439757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-124402183169092182960935579191096659000000000000)
      constant := (4704898885731354048403126138615476304376994334041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree138.table
  base := (7312100377472898297219451613572970839931/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-62217550913715883655121184756910798250000000000)
      constant := (2353648931812680851789355376034160448915735533515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146081077357154240681/25000000000000000000)
  centralHi := (23372972377144678509/4000000000000000000)
  directionLo := (586453002487307389609/100000000000000000000)
  directionHi := (58645300248730738961/10000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree139.table
  base := (29881404384223333536746945881301258243719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-250606362320613508493663388291915288000000000000)
      constant := (9549046239298750197089917292449048345091182603735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree139.table
  base := (14940702192111665982079320844021457294827/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-125336338359648799352292881500006675250000000000)
      constant := (4776956982237488312320936925928068063254405609755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586453002487307389609/100000000000000000000)
  centralHi := (58645300248730738961/10000000000000000000)
  directionLo := (73571749595157684271/12500000000000000000)
  directionHi := (588573996761261474169/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree140.table
  base := (38151089113138070435947856022476820749713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-63102089575760662766363904550409314500000000000)
      constant := (2422330490243678588162483511812592440939692541069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree140.table
  base := (152604356452552275496289200388476169150101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-252475149783731662788686786972383508000000000000)
      constant := (9694259959159189965251338492321090007666777270913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73571749595157684271/12500000000000000000)
  centralHi := (588573996761261474169/100000000000000000000)
  directionLo := (590687375183076938313/100000000000000000000)
  directionHi := (295343687591538469157/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree141.table
  base := (249334417830031423035892212188086259637/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-254210354285471793637247848111359228000000000000)
      constant := (9830624936490611940070845474463484196350525300625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree141.table
  base := (155834011143769634433731382218373893746723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-254277622848165726872787810944753665500000000000)
      constant := (9835633711303374805772245623769751979436011298199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590687375183076938313/100000000000000000000)
  centralHi := (295343687591538469157/50000000000000000000)
  directionLo := (592793219207018900803/100000000000000000000)
  directionHi := (148198304801754725201/25000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree142.table
  base := (159095985994773438422715728856520042568311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-256012350267900936209040078021081198000000000000)
      constant := (9972955165846454044290826868210999403204740023643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree142.table
  base := (31819197198954686895841039199181551414487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-256080095912599790956888834917123823000000000000)
      constant := (9978035220907542231303290454411802524201459567655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592793219207018900803/100000000000000000000)
  centralHi := (148198304801754725201/25000000000000000000)
  directionLo := (594891608845652173421/100000000000000000000)
  directionHi := (297445804422826086711/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree143.table
  base := (634337035178001002875798364934146712879/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-32226793281291259847604038491350396000000000000)
      constant := (1264539081130281433427664347035964193752479786464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree143.table
  base := (20298785125696031700419986997877746962153/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-32235321122129231880123732361186747562500000000)
      constant := (1265183060996462880510441322880503827582059851789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594891608845652173421/100000000000000000000)
  centralHi := (297445804422826086711/50000000000000000000)
  directionLo := (74622827838164334341/12500000000000000000)
  directionHi := (596982622705314674729/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree144.table
  base := (5178653005504954876669189124885572915399/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-32452042779094902669078067230065642250000000000)
      constant := (1282587173259751842173030222971525974454493522348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree144.table
  base := (82858448088079276782354496486160671466523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-129842521020733959562545441430932069000000000000)
      constant := (5132960756247933886068178675204153421481136735599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74622827838164334341/12500000000000000000)
  centralHi := (596982622705314674729/100000000000000000000)
  directionLo := (299533169010238228903/50000000000000000000)
  directionHi := (599066338020476457807/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree145.table
  base := (84537915753274342730419156750923126874579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-130709169107594181962208383875123554000000000000)
      constant := (5203054688476877058170318124878248286548905977927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree145.table
  base := (84537915753274341741963743249802769821089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-130743757552950991604595953417117147750000000000)
      constant := (5205703147240023338851727027092149041738661778557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299533169010238228903/50000000000000000000)
  centralHi := (599066338020476457807/100000000000000000000)
  directionLo := (601142830687026843267/100000000000000000000)
  directionHi := (150285707671756710817/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree146.table
  base := (21558385874592860611502653493245103570249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-32902541774702188312026124707496134750000000000)
      constant := (1319068577708684951111600984877930105820705953637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree146.table
  base := (43116771749185720830432619130966435559761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-65822497042584011823323232701651113250000000000)
      constant := (2639479708481062441362810883382884847238599332493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601142830687026843267/100000000000000000000)
  centralHi := (150285707671756710817/25000000000000000000)
  directionLo := (301606087647265123611/50000000000000000000)
  directionHi := (603212175294530247223/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree147.table
  base := (87945331323372644251453100982293317539457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-132511165090023324534000613784845524000000000000)
      constant := (5350007560112600485024432380567703661754230750141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree147.table
  base := (175890662646745287255658560655237835062717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-265092461234770111377393954778974610500000000000)
      constant := (10705459130828486790438794890598676323846467848521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301606087647265123611/50000000000000000000)
  centralHi := (603212175294530247223/100000000000000000000)
  directionLo := (75659305644686186229/12500000000000000000)
  directionHi := (605274445157489489833/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree148.table
  base := (179346558456559927943812988470442420767459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-266824326162475791639793457479413018000000000000)
      constant := (10848508872620927712943312839222035025794366233367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree148.table
  base := (179346558456559926953197277185323429571091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-266894934299204175461494978751344768000000000000)
      constant := (10854027185192767265841118678850569841370530747783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75659305644686186229/12500000000000000000)
  centralHi := (605274445157489489833/100000000000000000000)
  directionLo := (151832428086413414471/25000000000000000000)
  directionHi := (121465942469130731577/20000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree149.table
  base := (182834774426190735527011221866490927410201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-268626322144904934211585687389134988000000000000)
      constant := (10998029878856669116311303602125802077449166612213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree149.table
  base := (182834774426190734740259133164189241799797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-268697407363638239545596002723714925500000000000)
      constant := (11003622997017100470425558286785149015551569398561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151832428086413414471/25000000000000000000)
  centralHi := (121465942469130731577/20000000000000000000)
  directionLo := (609378047713405969299/100000000000000000000)
  directionHi := (6093780477134059693/1000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree150.table
  base := (186355310555641547290080812000460664186247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-270428318127334076783377917298856958000000000000)
      constant := (11148578138932434231716979093662236689202502842411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree150.table
  base := (46588827638910386666316601136406114268281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-67624970107018075907424256674021270750000000000)
      constant := (2788561641575373863945459886558140551835046335253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609378047713405969299/100000000000000000000)
  centralHi := (6093780477134059693/1000000000000000000)
  directionLo := (122283904185653108721/20000000000000000000)
  directionHi := (305709760464132771803/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree151.table
  base := (18990816684491610595616305491877284567113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-136115157054881609677585073604289464000000000000)
      constant := (5650076826424115945269259458409661481221296036345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree151.table
  base := (5934630213903628295624270206489002724093/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-34037794186563295964224756333556905062500000000)
      constant := (1413237236630745131663559137184380211397424149036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122283904185653108721/20000000000000000000)
  centralHi := (305709760464132771803/50000000000000000000)
  directionLo := (613454200498535515611/100000000000000000000)
  directionHi := (153363550124633878903/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree152.table
  base := (96746671647009031896439698706999146579051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-137016155046096180963481188559150449000000000000)
      constant := (5726378210302035355357041058263809655256834267263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree152.table
  base := (96746671647009031699429073516118356490481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-137052413278470215898949537320412699000000000000)
      constant := (5729288488625252940479886940107359636513573343853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613454200498535515611/100000000000000000000)
  centralHi := (153363550124633878903/25000000000000000000)
  directionLo := (615482153800128535481/100000000000000000000)
  directionHi := (307741076900064267741/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree153.table
  base := (98555419951475492686090423319102737827731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-137917153037310752249377303514011434000000000000)
      constant := (5803193221099979551626991862313119734888905828103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree153.table
  base := (197110839902950985059302413286396984517631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-275907299621374495882000098613195555500000000000)
      constant := (11612283818915138349758894401560340915344225836803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615482153800128535481/100000000000000000000)
  centralHi := (307741076900064267741/50000000000000000000)
  directionLo := (30875172355129968651/5000000000000000000)
  directionHi := (617503447102599373021/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree154.table
  base := (20076065667171835023373203017494805321369/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-138818151028525323535273418468872419000000000000)
      constant := (5880521858817952639262625206000747621343857350985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree154.table
  base := (100380328335859174992648435257300274670539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-138854886342904279983050561292782856500000000000)
      constant := (5883509209019933335041530730859664397922424541407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30875172355129968651/5000000000000000000)
  centralHi := (617503447102599373021/100000000000000000000)
  directionLo := (154879536398603270861/25000000000000000000)
  directionHi := (123903629118882616689/20000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree155.table
  base := (40888558720064711090932570496893973789999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-279438298039479789642339066847466808000000000000)
      constant := (11916728246911917252315239903906535984632704551935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree155.table
  base := (12777674600020222203587872773825920994227/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-34939030718780328006275268319741983812500000000)
      constant := (1490347596828087357215967121752389712441230033302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154879536398603270861/25000000000000000000)
  centralHi := (123903629118882616689/20000000000000000000)
  directionLo := (310763156703737996369/50000000000000000000)
  directionHi := (621526313407475992739/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree156.table
  base := (20815725068876991812866342428736875410829/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-140620147010954466107065648378594389000000000000)
      constant := (6036720015014001425840672801784561852993862245885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree156.table
  base := (208157250688769917972048473331784187377703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-281314718814676688134303170530306028000000000000)
      constant := (12079570888669642739756752941523934558480863908939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310763156703737996369/50000000000000000000)
  centralHi := (621526313407475992739/100000000000000000000)
  directionLo := (38970500852559726211/6250000000000000000)
  directionHi := (623528013640955619377/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree157.table
  base := (211904027937060677757474732613704586784623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-283042290004338074785923526666910748000000000000)
      constant := (12231179066984169720593989066618219085886624630899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree157.table
  base := (211904027937060677633133143281148456810117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-283117191879110752218404194502676185500000000000)
      constant := (12237388760174705960145645991908131675009715604721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38970500852559726211/6250000000000000000)
  centralHi := (623528013640955619377/100000000000000000000)
  directionLo := (312761654192207281341/50000000000000000000)
  directionHi := (625523308384414562683/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree158.table
  base := (215683125345198998557854234481300237851731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-284844285986767217357715756576632718000000000000)
      constant := (12389945357780425325380166006480018202138036540103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree158.table
  base := (5392078133629974961478487451289550231127/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2949516250000000000000000000000000000000000000
      center := (42473034)
      previous := (21236517)
      next := (21236517)
      square := (213408322441490885969760103787232500000000000)
      linear := (-35614958117943102037813152309380792875000000000)
      constant := (1549529298642486998153184406227069695799163869255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312761654192207281341/50000000000000000000)
  centralHi := (625523308384414562683/100000000000000000000)
  directionLo := (156878064685070588367/25000000000000000000)
  directionHi := (627512258740282353469/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree159.table
  base := (219494542913187971687084596828629158704757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6411024)
      previous := (3205512)
      next := (3205512)
      square := (32212576972300511089775110005620000000000000)
      linear := (-5408420414513138866594490311063296000000000000)
      constant := (236787526460693904905184634881834211524694486397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree159.table
  base := (2194945429131879716087181476083509056603/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1602756)
      previous := (801378)
      next := (801378)
      square := (8053144243075127772443777501405000000000000)
      linear := (-1352462915131975850880218124751964625000000000)
      constant := (59226923469647264664784800740477281031006804075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156878064685070588367/25000000000000000000)
  centralHi := (627512258740282353469/100000000000000000000)
  directionLo := (629494924845688276891/100000000000000000000)
  directionHi := (157373731211422069223/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree160.table
  base := (111669140320515308695027420692850761475293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-144224138975812751250650108198038329000000000000)
      constant := (6355279850446615875493475656310609303837000541609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree160.table
  base := (223338280641030617327844702692182269455943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-288524611072412944470707266419786658000000000000)
      constant := (12717008919450685457884020762188769061377746030059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629494924845688276891/100000000000000000000)
  centralHi := (157373731211422069223/25000000000000000000)
  directionLo := (315735682946838619149/50000000000000000000)
  directionHi := (631471365893677238299/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree161.table
  base := (113607169264364943535441856380579732018503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-145125136967027322536546223152899314000000000000)
      constant := (6436203876604898331294094920727133141582375919339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree161.table
  base := (56803584632182471755375242566671264295983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-72581771034211752138702072598039203875000000000)
      constant := (3219734455199074749061991900478534058900643584579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315735682946838619149/50000000000000000000)
  centralHi := (631471365893677238299/100000000000000000000)
  directionLo := (633441640153829847553/100000000000000000000)
  directionHi := (316720820076914923777/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree162.table
  base := (46224543315257733058396203262077083909463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-292052269916483787644884676215520598000000000000)
      constant := (13035283059366478501229462723280386256974298589095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree162.table
  base := (115561358288144332626391121076047141563721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-146064778600640536319454657182263486500000000000)
      constant := (6520947239801033765239398623487552652002846399973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633441640153829847553/100000000000000000000)
  centralHi := (316720820076914923777/50000000000000000000)
  directionLo := (4964107851502398779/781250000000000000)
  directionHi := (635405804992307043713/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree163.table
  base := (235063414783709771703358488443229408368869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-293854265898912930216676906125242568000000000000)
      constant := (13199185619363283920193593101484833961719492087697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree163.table
  base := (47012682956741954334448935362558995238511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-293932030265715136723010338336897130500000000000)
      constant := (13205878895867997713860617466114299217799268281215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4964107851502398779/781250000000000000)
  centralHi := (635405804992307043713/100000000000000000000)
  directionLo := (637363916891338767773/100000000000000000000)
  directionHi := (318681958445669383887/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree164.table
  base := (239036433150995962904910949202574856137097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-295656261881342072788469136034964538000000000000)
      constant := (13364115433200219423989528592073457686014223863461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree164.table
  base := (119518216575497981440107730834796531167237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-147867251665074600403555681154633644000000000000)
      constant := (6685445534797048025451698047511644055172117599281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637363916891338767773/100000000000000000000)
  centralHi := (318681958445669383887/50000000000000000000)
  directionLo := (319658015734087707233/50000000000000000000)
  directionHi := (639316031468175414467/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree165.table
  base := (243041771678149934244293714624529562208033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-297458257863771215360261365944686508000000000000)
      constant := (13530072500877291372594636198284165862620383371229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree165.table
  base := (60760442919537483556173318401408075466189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-74384244098645816222803096570409361375000000000)
      constant := (3384232750195092225396327583914584369835156874857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319658015734087707233/50000000000000000000)
  centralHi := (639316031468175414467/100000000000000000000)
  directionLo := (641262203493520052773/100000000000000000000)
  directionHi := (320631101746760026387/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree166.table
  base := (61769857591293580388231386640999134979861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5899032500000000000000000000000000000000000000
      center := (84946068)
      previous := (42473034)
      next := (42473034)
      square := (426816644882981771939520207574465000000000000)
      linear := (-74815063461550089483013398963602119500000000000)
      constant := (3424264205598626496387749359758422938887234753793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree166.table
  base := (123539715182587160768684769778570212281933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-149669724729508664487656705127003801500000000000)
      constant := (6851999344713411242724542545503360223469458771929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641262203493520052773/100000000000000000000)
  centralHi := (320631101746760026387/50000000000000000000)
  directionLo := (321601243454729348609/50000000000000000000)
  directionHi := (643202486909458697219/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree167.table
  base := (251149409212071702822549325530790487328519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-301062249828629500503845825764130448000000000000)
      constant := (13865068397751869345921442707830440753926708703147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree167.table
  base := (251149409212071702810203655750442668673011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-301141922523451393059414434226377760500000000000)
      constant := (13872094135533462885558061647876224987521154504743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321601243454729348609/50000000000000000000)
  centralHi := (643202486909458697219/100000000000000000000)
  directionLo := (645136934846905236261/100000000000000000000)
  directionHi := (322568467423452618131/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree168.table
  base := (255251708218844599824686293790107581058451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-302864245811058643075638055673852418000000000000)
      constant := (14034107226949387404110836557699519203664074739463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree168.table
  base := (51050341643768919962977757232419272185123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-302944395587885457143515458198747918000000000000)
      constant := (14041217339100296052317510227997067464492773186995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell138.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645136934846905236261/100000000000000000000)
  centralHi := (322568467423452618131/50000000000000000000)
  directionLo := (32353279982128848937/5000000000000000000)
  directionHi := (647065599642576978741/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree169.table
  base := (259386327385495479675224976035450485118583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23596130000000000000000000000000000000000000000
      center := (339784272)
      previous := (169892136)
      next := (169892136)
      square := (1707266579531927087758080830297860000000000000)
      linear := (-304666241793487785647430285583574388000000000000)
      constant := (14204173309987065981557902058058537006292114988379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree169.table
  base := (129693163692747739833724981044766288400851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11798065000000000000000000000000000000000000000
      center := (169892136)
      previous := (84946068)
      next := (84946068)
      square := (853633289765963543879040415148930000000000000)
      linear := (-152373434326159760613808241085559037750000000000)
      constant := (7105684150063663903583238001772036555080209730663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell138.Kernel169
