import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell186.Parameters
import ForestUnimodality.BinomialMassData.Q7977_15052.Batch000_049
import ForestUnimodality.BinomialMassData.Q7977_15052.Batch050_099
import ForestUnimodality.BinomialMassData.Q7977_15052.Batch100_149
import ForestUnimodality.BinomialMassData.Q7977_15052.Batch150_199
import ForestUnimodality.BinomialMassData.Q95749_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95749_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95749_180624.Batch100_149
import ForestUnimodality.BinomialMassData.Q95749_180624.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree000.table
  base := (175883872494781779185473169/2000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78592633948597057091944862500000000000)
      linear := (-6000443187240728400155820250000000000)
      constant := (109927420309238611990920730625000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree000.table
  base := (175883872494781779185473169/2000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78592633948597057091944862500000000000)
      linear := (-6000443187240728400155820250000000000)
      constant := (109927420309238611990920730625000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree001.table
  base := (95684231686219420748092622743480289550333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-10116340470901613582641077947770928000000000000)
      constant := (6777385216608272652527760718522777237758246431385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree001.table
  base := (95663339135105391506786589017898417816787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-91069245044230665048207475668757414500000000000)
      constant := (60983166660291313758539167203521129591777298065135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49909309499817069173/100000000000000000000)
  directionHi := (24954654749908534587/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree002.table
  base := (138824997461466706777292014706041734891421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-9776471312476704151323853783476439000000000000)
      constant := (1971146709556562607364530099170906915115718010149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree002.table
  base := (277545657178432405525182955089817955666267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-176020845236812960332704916380214027000000000000)
      constant := (35467392530784412726414505657009937813782134872107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49909309499817069173/100000000000000000000)
  centralHi := (24954654749908534587/50000000000000000000)
  directionLo := (70582422383317652007/100000000000000000000)
  directionHi := (8822802797914706501/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree003.table
  base := (174103668447933960251943607073060797719891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-28989544779005203022654337186134828000000000000)
      constant := (2488922793063962462697770236066896520738471221579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree003.table
  base := (174023319907159665822972956061860965662427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-28996938381043917290800261899074515500000000000)
      constant := (2487797082930572763598168636192882157986288270163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70582422383317652007/100000000000000000000)
  centralHi := (8822802797914706501/12500000000000000000)
  directionLo := (86445459824363193923/100000000000000000000)
  directionHi := (21611364956090798481/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree004.table
  base := (59137122493576034965464293466577732241267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-19213073466528498871330483402658389000000000000)
      constant := (858116312955825145999578850376942321173089494123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree004.table
  base := (59108466017186359405418257019312276989573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-172962022810988775450849898901563626000000000000)
      constant := (7719490537436154239218942209749514179399484260533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86445459824363193923/100000000000000000000)
  centralHi := (21611364956090798481/25000000000000000000)
  directionLo := (49909309499817069173/50000000000000000000)
  directionHi := (99818618999634138347/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree005.table
  base := (43137332455098135728378541842137490105219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-23931374543554396231333798212249364000000000000)
      constant := (642989058188383967603044659150785735500728822011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree005.table
  base := (17246820908474408058976974270413158190563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-430875645814559846186197238514583864500000000000)
      constant := (11568932119536550260332123556283400574922907831615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49909309499817069173/50000000000000000000)
  centralHi := (99818618999634138347/100000000000000000000)
  directionLo := (111600608751666994379/100000000000000000000)
  directionHi := (5580030437583349719/5000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree006.table
  base := (4156646194064979999186379114788887845451/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-7162418905145073397834278255460084750000000000)
      constant := (129240160308931846300747093658263467177264082438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree006.table
  base := (2077399738229980622319538191757900507299/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-7164267305654751964870759433695006625000000000)
      constant := (129193809472144410151878569980235801456970794124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111600608751666994379/100000000000000000000)
  centralHi := (5580030437583349719/5000000000000000000)
  directionLo := (15281542711149117489/12500000000000000000)
  directionHi := (122252341689192939913/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree007.table
  base := (26639391627946193179951255328314581864453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-33367976697606190951340427831431314000000000000)
      constant := (439741952296138157687242592133664459239989572557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree007.table
  base := (53256223373836639944130546376578515381881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-600778846199724436755192119937497089500000000000)
      constant := (7913062073125029495601434125920786867141935481001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15281542711149117489/12500000000000000000)
  centralHi := (122252341689192939913/100000000000000000000)
  directionLo := (132047621043469436797/100000000000000000000)
  directionHi := (66023810521734718399/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree008.table
  base := (2187632982572510615772430599331714188023/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-19043138887316044155671871320511144500000000000)
      constant := (195615120224773048885725054078876630810517279435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree008.table
  base := (43734560831359774526997591011623916033567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-685730446392306732039689560648953702000000000000)
      constant := (7040596979201515072843946833619687805294065535407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132047621043469436797/100000000000000000000)
  centralHi := (66023810521734718399/50000000000000000000)
  directionLo := (70582422383317652007/50000000000000000000)
  directionHi := (28232968953327060803/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree009.table
  base := (9118303264076118139318209248170152299873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-21402289425828992835673528725306632000000000000)
      constant := (180562857851220160761781424437190277509440358537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree009.table
  base := (2278629906898864124591836842932140235747/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-10703917313679014268391486130005698812500000000)
      constant := (90267972405962311949407336833684526549520347486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70582422383317652007/50000000000000000000)
  centralHi := (28232968953327060803/20000000000000000000)
  directionLo := (149727928499451207519/100000000000000000000)
  directionHi := (935799553121570047/625000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree010.table
  base := (15332510141903843615196103888042553434863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-47522879928683883031350372260204239000000000000)
      constant := (343938316370097399858253584699238025829190571847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree010.table
  base := (7662996855068028250652901574541192531429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-213908411694367830652171110517966731750000000000)
      constant := (1547603221947078719696646775836808343124777063509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149727928499451207519/100000000000000000000)
  centralHi := (935799553121570047/625000000000000000)
  directionLo := (157827094465700988127/100000000000000000000)
  directionHi := (4932096702053155879/3125000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree011.table
  base := (12945774821564799692989157255320932978947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-52241181005709780391353687069795214000000000000)
      constant := (336577361194511238421104998062157511094562962043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree011.table
  base := (25880121722081919853443250552991294862723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-940585246970053617893181882783323539500000000000)
      constant := (6058367964954734958202124716172940394143030321683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157827094465700988127/100000000000000000000)
  centralHi := (4932096702053155879/3125000000000000000)
  directionLo := (3310609063132271063/2000000000000000000)
  directionHi := (165530453156613553151/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree012.table
  base := (10944897505366966849682984314076663595061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-56959482082735677751357001879386189000000000000)
      constant := (337180744597027569098222619691866278462211325309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree012.table
  base := (683739904986425728108288031054882428141/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-14243567321703276571912212826316391000000000000)
      constant := (84300931181930923923293572101805234424177663316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3310609063132271063/2000000000000000000)
  centralHi := (165530453156613553151/100000000000000000000)
  directionLo := (172890919648726387847/100000000000000000000)
  directionHi := (21611364956090798481/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree013.table
  base := (3697825494035303748864706748675037070957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-123355566319523150222720633377954328000000000000)
      constant := (689080798862156437318801894815120187780080558665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree013.table
  base := (2310016461577999366084382195867520870583/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-138811055919402276057772095525779595562500000000)
      constant := (775322327066479188982452236644292131256107301743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172890919648726387847/100000000000000000000)
  centralHi := (21611364956090798481/12500000000000000000)
  directionLo := (179950574524592431259/100000000000000000000)
  directionHi := (8997528726229621563/5000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree014.table
  base := (15570813747503280530395235387472667523281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-132792168473574944942727262997136278000000000000)
      constant := (715631368168213388265921808913892297010470394489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree014.table
  base := (1945351081038146981429407163223131438611/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-149430005943475062968334275614711672125000000000)
      constant := (805247283385004858709598846952764122552316467331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179950574524592431259/100000000000000000000)
  centralHi := (8997528726229621563/5000000000000000000)
  directionLo := (46685884139694345667/25000000000000000000)
  directionHi := (186743536558777382669/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree015.table
  base := (1630911826797606220208441896304287917753/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-17778596328453342457841736577039778500000000000)
      constant := (94096667955189486683532283586187319058790580257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree015.table
  base := (6520088830314074408256598205645995528413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-71132869318910155501731758090508332750000000000)
      constant := (376483945514313294461351758151898363394634881797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46685884139694345667/25000000000000000000)
  centralHi := (186743536558777382669/100000000000000000000)
  directionLo := (24162240564187891559/12500000000000000000)
  directionHi := (193297924513503132473/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree016.table
  base := (10851162812411322004577931859477846370517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-151665372781678534382740522235500178000000000000)
      constant := (799552227111322956900716984623034004362557337373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree016.table
  base := (2711211764550186302080362165631023581067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-341335811983241273578917271585151650500000000000)
      constant := (1799547093989921161970828650104757565458045282907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24162240564187891559/12500000000000000000)
  centralHi := (193297924513503132473/100000000000000000000)
  directionLo := (49909309499817069173/25000000000000000000)
  directionHi := (199637237999268276693/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree017.table
  base := (279030646311938603946934241641520601583/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-20137746866966291137843393981835266000000000000)
      constant := (106901416535819351381829496063049844635337790108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree017.table
  base := (1784677676260655057690472790807438374991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-1450294848125547389600166527052063214500000000000)
      constant := (7699601333014810418502976589203076809066232006555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49909309499817069173/25000000000000000000)
  centralHi := (199637237999268276693/100000000000000000000)
  directionLo := (102890677384694352963/50000000000000000000)
  directionHi := (205781354769388705927/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree018.table
  base := (1809393782029291030308783375877609783509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-42634644272445530955688445368466019500000000000)
      constant := (229784830211525178610032770069296753850540853021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree018.table
  base := (7232634916462059725653731541404124044051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-170582938702014409431629329751502203000000000000)
      constant := (919494295422373302746919226800441186823225604619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102890677384694352963/50000000000000000000)
  centralHi := (205781354769388705927/100000000000000000000)
  directionLo := (105873633574976478011/50000000000000000000)
  directionHi := (211747267149952956023/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree019.table
  base := (5741649801448273156431959790916064488591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-179975179243833918542760411093046028000000000000)
      constant := (990836390517820580893137047118428463723347131879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree019.table
  base := (5737295572974170354474284297577482244087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-1620198048510711980169161408474976439500000000000)
      constant := (8921232803042402441982354822373489889365065536327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105873633574976478011/50000000000000000000)
  centralHi := (211747267149952956023/100000000000000000000)
  directionLo := (217549636451597125169/100000000000000000000)
  directionHi := (21754963645159712517/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree020.table
  base := (110303384705885135231495806941568524253/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-23676472674735714157845880089028497250000000000)
      constant := (133736364363305324615055030614822393392515393785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree020.table
  base := (4408305908733522355750004827036094628721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-1705149648703294275453658849186433052000000000000)
      constant := (9633249749028922677573949607355957705134134524641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217549636451597125169/100000000000000000000)
  centralHi := (21754963645159712517/10000000000000000000)
  directionLo := (111600608751666994379/50000000000000000000)
  directionHi := (223201217503333988759/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree021.table
  base := (100780671286913714750983586272352165869/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-24856047943992188497846708791426241000000000000)
      constant := (144495292022514731205721192936622791378634287444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree021.table
  base := (3221620267810282131496237229193195853121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-198900138766208507859795143321987740500000000000)
      constant := (1156492786866197752054776701502107995633417537449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111600608751666994379/50000000000000000000)
  centralHi := (223201217503333988759/100000000000000000000)
  directionLo := (2858914858323628917/1250000000000000000)
  directionHi := (228713188665890313361/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree022.table
  base := (2160232354179223941338375707923476362237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-208284985705989302702780299950591878000000000000)
      constant := (1248768077884659884677977443507942630356781138053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree022.table
  base := (134830475522231343456716031093530813383/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-234381606136057358252831716326168284625000000000)
      constant := (1405530776278029324239745663902996685306105851086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2858914858323628917/1250000000000000000)
  centralHi := (228713188665890313361/100000000000000000000)
  directionLo := (234095411839847189357/100000000000000000000)
  directionHi := (117047705919923594679/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree023.table
  base := (300324580224853254605929218558136681093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-54430396965010274355696732392443457000000000000)
      constant := (337018306814494913564380802177800111166875984717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree023.table
  base := (1198722828926217189441048371395501726443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-1960004449281041161307151171320802889500000000000)
      constant := (12138569503760380156622440812590118243029146839803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234095411839847189357/100000000000000000000)
  centralHi := (117047705919923594679/50000000000000000000)
  directionLo := (119678319902996839731/50000000000000000000)
  directionHi := (239356639805993679463/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree024.table
  base := (334369894406578458023581743598437270113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-227158190014092892142793559188955778000000000000)
      constant := (1453682239631271042873997731633680911880698729097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree024.table
  base := (332120871604794955402774429293458482799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-227217338830402606287960956892473278000000000000)
      constant := (1454405069425086279877200433714719494710917433031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119678319902996839731/50000000000000000000)
  centralHi := (239356639805993679463/100000000000000000000)
  directionLo := (9780187335135435193/4000000000000000000)
  directionHi := (122252341689192939913/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree025.table
  base := (-113014782014510604480685371805304489379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-59148698042036171715700047202034432000000000000)
      constant := (391358046307230426193792185220294345521434654949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree025.table
  base := (-454020247057743489840832586743784375009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-2129907649666205751876146052743716114500000000000)
      constant := (14096008743155143574145101022496218015155943651311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9780187335135435193/4000000000000000000)
  centralHi := (122252341689192939913/50000000000000000000)
  directionLo := (124773273749542672933/50000000000000000000)
  directionHi := (249546547499085345867/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree026.table
  base := (-58379146918124749431717853213291511779/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-61507848580549120395701704606829919500000000000)
      constant := (420796802168165422922906158075288552734719346745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree026.table
  base := (-1169290750549843295993591187057683448583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-2214859249858788047160643493455172727000000000000)
      constant := (15156436666080383946570004839315476472638557185257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124773273749542672933/50000000000000000000)
  centralHi := (249546547499085345867/100000000000000000000)
  directionLo := (254488543049508987193/100000000000000000000)
  directionHi := (127244271524754493597/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree027.table
  base := (-455051575960273330539948099717187851341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-63866999119062069075703362011625407000000000000)
      constant := (451708490276057859230180189386999655257764563371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree027.table
  base := (-1821691715319728385039313678629947680721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-255534538894596704716126770462958815500000000000)
      constant := (1807767747138810966867034775123331435332957598151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254488543049508987193/100000000000000000000)
  centralHi := (127244271524754493597/50000000000000000000)
  directionLo := (259336379473089581771/100000000000000000000)
  directionHi := (64834094868272395443/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree028.table
  base := (-2416611364624212098371630223710900323687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-264904598630300071022820077665683578000000000000)
      constant := (1936277822290103152962140446660466978274437376897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree028.table
  base := (-1208950940674751594023073002710580465487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-1192381225121976318864819187439042976000000000000)
      constant := (8717788384440102469184430629565709890060448714273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259336379473089581771/100000000000000000000)
  centralHi := (64834094868272395443/25000000000000000000)
  directionLo := (132047621043469436797/50000000000000000000)
  directionHi := (52819048417387774719/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree029.table
  base := (-2892948004102975369849857076243660179/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-34292650098043983217853338410608191000000000000)
      constant := (258929971186077096292503541088838990089659087872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree029.table
  base := (-1481749388572692717690135650344391917533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-1234857025218267466507067907794771282250000000000)
      constant := (9326363495628424705375807711456455295498550412307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132047621043469436797/50000000000000000000)
  centralHi := (52819048417387774719/20000000000000000000)
  directionLo := (134384928533399328587/50000000000000000000)
  directionHi := (10750794282671946287/4000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree030.table
  base := (-865542787224381861295272021972403189257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-70944450734600915115708334226011869500000000000)
      constant := (553063444624995706553620852229816330003981895567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree030.table
  base := (-3463142253469592490144241550876156624467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-283851738958790803144292584033444353000000000000)
      constant := (2213418503656718014318352995924504965689577745077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134384928533399328587/50000000000000000000)
  centralHi := (10750794282671946287/4000000000000000000)
  directionLo := (273364546425566880651/100000000000000000000)
  directionHi := (68341136606391720163/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree031.table
  base := (-979971440277658891271819196303441432931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-73303601273113863795709991630807357000000000000)
      constant := (589666166013263290428786379180096959465594874661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree031.table
  base := (-3920726985031216163684534801842236797921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-2639617250821699523583130697012455789500000000000)
      constant := (21239199050572316199742905660196948785633903122159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273364546425566880651/100000000000000000000)
  centralHi := (68341136606391720163/25000000000000000000)
  directionLo := (34735409350816918033/12500000000000000000)
  directionHi := (55576654961307068853/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree032.table
  base := (-2169390601305240339812844797785158328227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-151325503623253624951423298071205689000000000000)
      constant := (1255313141841391819328990537682264380380548209637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree032.table
  base := (-4339509298387223322165815534573756287513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-2724568851014281818867628137723912402000000000000)
      constant := (22607609553033119072814173235630498176036029972727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34735409350816918033/12500000000000000000)
  centralHi := (55576654961307068853/20000000000000000000)
  directionLo := (282329689533270608029/100000000000000000000)
  directionHi := (28232968953327060803/10000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree033.table
  base := (-4721583046098380411857994440456233957057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-312087609400559044622853225761593328000000000000)
      constant := (2668100042819101812977758569661412282814534137367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree033.table
  base := (-4722212725790468853816567453169447915441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-312168939022984901572458397603929890500000000000)
      constant := (2669516772133341596058984081205237379708782730471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282329689533270608029/100000000000000000000)
  centralHi := (28232968953327060803/10000000000000000000)
  directionLo := (28670715506715471831/10000000000000000000)
  directionHi := (286707155067154718311/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree034.table
  base := (-2535285875362719752307144262692405192973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-160762105777305419671429927690387639000000000000)
      constant := (1415526824887515222489651142447271223451024707563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree034.table
  base := (-253555795492185464731232635415556821811/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-723618012849861602359155754786706406750000000000)
      constant := (6373258211348517845788492938956410143973025927345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28670715506715471831/10000000000000000000)
  centralHi := (286707155067154718311/100000000000000000000)
  directionLo := (29101878279837889497/10000000000000000000)
  directionHi := (291018782798378894971/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree035.table
  base := (-2693827965011275453648101937234261424529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-165480406854331317031433242499978614000000000000)
      constant := (1499730039130208201889088331363337252513488614599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree035.table
  base := (-5388125852267521104773059473384951390273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-2979423651592028704721120459858282239500000000000)
      constant := (27009512210415290247601002359424670582640669274767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29101878279837889497/10000000000000000000)
  centralHi := (291018782798378894971/100000000000000000000)
  directionLo := (295267456920329373033/100000000000000000000)
  directionHi := (147633728460164686517/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree036.table
  base := (-5674433439506209570605774379184630180861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-340397415862714428782873114619139178000000000000)
      constant := (3173296702371108538584794234610762812436507674491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree036.table
  base := (-2837419491326871953093674420722898857703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-170243069543589500000312105587207714000000000000)
      constant := (1587493644047132083736982782620382600880018568193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295267456920329373033/100000000000000000000)
  centralHi := (147633728460164686517/50000000000000000000)
  directionLo := (299455856998902415039/100000000000000000000)
  directionHi := (935799553121570047/312500000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree037.table
  base := (-9269128646889525611265637704472668361/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-43729252252095777937859968029790141000000000000)
      constant := (419068071878067748643184828656151997403932959280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree037.table
  base := (-5932592097669454554458906351621647874649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-3149326851977193295290115341281195464500000000000)
      constant := (30188982629292813157047571411448415451156439098871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299455856998902415039/100000000000000000000)
  centralHi := (935799553121570047/312500000000000000)
  directionLo := (151793238869272124489/50000000000000000000)
  directionHi := (303586477738544248979/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree038.table
  base := (-3081101697177749535979402236612797212129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-179635310085409009111443186928751539000000000000)
      constant := (1768593912887420689192326745150960510913524510199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree038.table
  base := (-1540626217649950292059956473386772097753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-808569613042443897643653195498163019250000000000)
      constant := (7962915156720528713498833754284854661972621997687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151793238869272124489/50000000000000000000)
  centralHi := (303586477738544248979/100000000000000000000)
  directionLo := (307661646359184903203/100000000000000000000)
  directionHi := (76915411589796225801/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree039.table
  base := (-1273051126739357280731927167572027572859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-368707222324869812942893003476685028000000000000)
      constant := (3727213158037081605541759361674775735228283734145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree039.table
  base := (-6365515341709310493068587051551135990767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-368803339151373098428790024744900965500000000000)
      constant := (3729200004482023563034708566887284305556881840377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307661646359184903203/100000000000000000000)
  centralHi := (76915411589796225801/25000000000000000000)
  directionLo := (19480221120487734857/6250000000000000000)
  directionHi := (311683537927803757713/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree040.table
  base := (-6542185954681798804903658259013368705969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-378143824478921607662899633095866978000000000000)
      constant := (3922609429136771374669314732017469545864167651239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree040.table
  base := (-3271204780334604603018462481936733109477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-1702090826277470090571803831707782651000000000000)
      constant := (17661150347147711059667175541720213121757191605483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19480221120487734857/6250000000000000000)
  centralHi := (311683537927803757713/100000000000000000000)
  directionLo := (157827094465700988127/50000000000000000000)
  directionHi := (63130837786280395251/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree041.table
  base := (-1673413482677523625738181693863847464561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-96895106658243350595726565678762232000000000000)
      constant := (1030841824850776259185987831681879061099094729191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree041.table
  base := (-1673461588581832260892810168067842891741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-872283313186880619107026276031755478625000000000)
      constant := (9282519656714545424504751327046621815113269871939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157827094465700988127/50000000000000000000)
  centralHi := (63130837786280395251/20000000000000000000)
  directionLo := (319575509331816201749/100000000000000000000)
  directionHi := (1278302037327264807/400000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree042.table
  base := (-6820212520587695836663364406744357101869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-397017028787025197102912892334230878000000000000)
      constant := (4329478938845939277229685513095582039641184744139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree042.table
  base := (-6820378029116858339702928622596153123851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-397120539215567196856955838315386503000000000000)
      constant := (4331784827917176355244213645143722205578891909181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319575509331816201749/100000000000000000000)
  centralHi := (1278302037327264807/400000000000000000)
  directionLo := (64689858660979705249/20000000000000000000)
  directionHi := (161724646652449263123/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree043.table
  base := (-3461162694993694527110353483202820650431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-203226815470538495911459760976706414000000000000)
      constant := (2270468890940493972075669912357097597188207117161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree043.table
  base := (-3461233840730237551623996041411313314763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-1829518226566343533498549992774967569750000000000)
      constant := (20445098074886081436267170356074891452598114025477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64689858660979705249/20000000000000000000)
  centralHi := (161724646652449263123/50000000000000000000)
  directionLo := (40909653604426533047/12500000000000000000)
  directionHi := (327277228835412264377/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree044.table
  base := (-1400076280070861684405495866022629784099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-415890233095128786542926151572594778000000000000)
      constant := (4757738322164470352068960655283309204163623236345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree044.table
  base := (-7000503676745552144156955280420524765517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-3743988053325269362281597426261391752000000000000)
      constant := (42842427228535238178934120283459243711014345168643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40909653604426533047/12500000000000000000)
  centralHi := (327277228835412264377/100000000000000000000)
  directionLo := (331060906313227106301/100000000000000000000)
  directionHi := (165530453156613553151/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree045.table
  base := (-1763676683068359936784283710550247989013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-106331708812295145315733195297944182000000000000)
      constant := (1244968985231044645773017428353384462671165776803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree045.table
  base := (-3527405881905793279614144230619697717501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-212718869639880647642560825942936020250000000000)
      constant := (2491261954089791312305898902312087330317834082331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331060906313227106301/100000000000000000000)
  centralHi := (165530453156613553151/50000000000000000000)
  directionLo := (334801826255000983137/100000000000000000000)
  directionHi := (167400913127500491569/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree046.table
  base := (-3542787516264875780616097449424612938229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-217381718701616187991469705405479339000000000000)
      constant := (2603673381637695588076180320894427797035090799299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree046.table
  base := (-7085665214099761147693237248710855564941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-3913891253710433952850592307684304977000000000000)
      constant := (46891025158887069002277453013650049108655104684739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334801826255000983137/100000000000000000000)
  centralHi := (167400913127500491569/50000000000000000000)
  directionLo := (338501406257688087591/100000000000000000000)
  directionHi := (42312675782211010949/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree047.table
  base := (-1773303977355739606047098906213440555841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-111050009889321042675736510107535157000000000000)
      constant := (1360036884481445092607558099470686809095337502871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree047.table
  base := (-7093293309944350671440421646916196483331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-3998842853903016248135089748395761589500000000000)
      constant := (48987327964258295915160940033645529225332571213549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338501406257688087591/100000000000000000000)
  centralHi := (42312675782211010949/12500000000000000000)
  directionLo := (34216098727526042479/10000000000000000000)
  directionHi := (342160987275260424791/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree048.table
  base := (-1415564409420518471340473609922551747117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-453636641711335965422952670049322578000000000000)
      constant := (5678275536435225171241709188588290895747890086135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree048.table
  base := (-1769472113172638548156698214157313004527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-113438734835988848428321866364089394500000000000)
      constant := (1420322196383606937378544052773739403769999914937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34216098727526042479/10000000000000000000)
  centralHi := (342160987275260424791/100000000000000000000)
  directionLo := (69156367859490555139/20000000000000000000)
  directionHi := (21611364956090798481/6250000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree049.table
  base := (-439972197806944990020756195471824770609/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-57884155483173470017869912458563066000000000000)
      constant := (740216058603813210541386816916382733113330654158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree049.table
  base := (-879951514568552511486210757547167874093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-521093256786022604838010578727334351812500000000)
      constant := (6665477237127849956820672708403652831252392209547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69156367859490555139/20000000000000000000)
  centralHi := (21611364956090798481/6250000000000000000)
  directionLo := (87341291624679871053/25000000000000000000)
  directionHi := (349365166498719484213/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree050.table
  base := (-6978551010430738166375780462845687818687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-472509846019439554862965929287686478000000000000)
      constant := (6170504412902916654662263815601453239566150721897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree050.table
  base := (-3489299918402316777587118516334824642521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-2126848827240381566994291035265065713500000000000)
      constant := (27781983586537030655414655705057189328070092485559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87341291624679871053/25000000000000000000)
  centralHi := (349365166498719484213/100000000000000000000)
  directionLo := (88228027979147065009/25000000000000000000)
  directionHi := (352912111916588260037/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree051.table
  base := (-3447461771927645463117817472584265125547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-240973224086745674791486279453434214000000000000)
      constant := (3212300877478426992110697303153060949956448262557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree051.table
  base := (-3447482694972327306974598204119341673363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-241036069704074746070726639513421557750000000000)
      constant := (3214001799895292980756904982425003318837999621653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88228027979147065009/25000000000000000000)
  centralHi := (352912111916588260037/100000000000000000000)
  directionLo := (71284752342187469431/20000000000000000000)
  directionHi := (89105940427734336789/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree052.table
  base := (-6788768445402622806097034879945877546819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-491383050327543144302979188526050378000000000000)
      constant := (6684019140144263035436350070272285569083737547589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree052.table
  base := (-3394402148668421811654168332314198876443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-2211800427432963862278788475976522326000000000000)
      constant := (30094000699378982419010533012835063119164613010197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71284752342187469431/20000000000000000000)
  centralHi := (89105940427734336789/25000000000000000000)
  directionLo := (179950574524592431259/50000000000000000000)
  directionHi := (359901149049184862519/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree053.table
  base := (-1665041513968680130118642766576455453549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (221804)
      previous := (110902)
      next := (110902)
      square := (792370935469755529600988103725000000000000)
      linear := (-44572770779778830457723906919298000000000000)
      constant := (618436759596458711364707088716486775558659491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree053.table
  base := (-416262297657975686766871892943290373821/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3565669209613899883204446466762500000000000)
      linear := (-200629781730976771975884406935942562500000000)
      constant := (2784436808194205710569325525499775587200855102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179950574524592431259/50000000000000000000)
  centralHi := (359901149049184862519/100000000000000000000)
  directionLo := (363345257656780362191/100000000000000000000)
  directionHi := (22709078603548772637/6250000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree054.table
  base := (-3254591921220887960629338273516377056283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-255128127317823366871496223882207139000000000000)
      constant := (3609404835827481626104349720287795107615310208173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree054.table
  base := (-3254605067085359203559888409692542012503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-255194669736171795284809546298664326500000000000)
      constant := (3611311748891504368338981305203707780094607406993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363345257656780362191/100000000000000000000)
  centralHi := (22709078603548772637/6250000000000000000)
  directionLo := (183378512533789409869/50000000000000000000)
  directionHi := (366757025067578819739/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree055.table
  base := (-3167939233336615266953593335594285372017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-259846428394849264231499538691798114000000000000)
      constant := (3747090530147161726072400547313414770573011409127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree055.table
  base := (-6335900971565890826198861061056570793413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-4678455655443674610411069274087414489500000000000)
      constant := (67483236769675444902541060745593573800496395498827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183378512533789409869/50000000000000000000)
  centralHi := (366757025067578819739/100000000000000000000)
  directionLo := (185068672802266273447/50000000000000000000)
  directionHi := (74027469120906509379/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree056.table
  base := (-767537189908352196160406105291663753227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-66141182367968790397875713375347272250000000000)
      constant := (971858615356445993814927375983230255463131384637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree056.table
  base := (-767539597151836610884284299541708477529/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-595425906954532113211945839349858887750000000000)
      constant := (8751341721104279855303868445511256232685109918391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185068672802266273447/50000000000000000000)
  centralHi := (74027469120906509379/20000000000000000000)
  directionLo := (373487073117554765337/100000000000000000000)
  directionHi := (186743536558777382669/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree057.table
  base := (-1480620243855636598953436789371499458221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-134641515274450529475753084155490032000000000000)
      constant := (2015218173317777201468511309333856480075682200651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree057.table
  base := (-370156090643879523405531187395325353561/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-67338317442067211124723113270976773812500000000)
      constant := (1008140241565425611719141130940274910564448601382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373487073117554765337/100000000000000000000)
  centralHi := (186743536558777382669/50000000000000000000)
  directionLo := (376807023502304465481/100000000000000000000)
  directionHi := (188403511751152232741/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree058.table
  base := (-284123120801451522022414605486881750733/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-137000665812963478155754741560285519500000000000)
      constant := (2088047974010472020476851035992309816633024230615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree058.table
  base := (-355154781639787925754012575815816983913/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-616663807002677687033070199527723040875000000000)
      constant := (9401165421256251806315727038401282907932801996654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376807023502304465481/100000000000000000000)
  centralHi := (188403511751152232741/50000000000000000000)
  directionLo := (380097977020944903837/100000000000000000000)
  directionHi := (190048988510472451919/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree059.table
  base := (-5420270052488809313881319755866253797921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-557439265405905707343025595860324028000000000000)
      constant := (8648826131685678090702868305843611550574546791351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree059.table
  base := (-5420282100045567103704759850251338825947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-5018262056214003791549059036933240939500000000000)
      constant := (77880408112732850862201420770069779133313085054613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380097977020944903837/100000000000000000000)
  centralHi := (190048988510472451919/50000000000000000000)
  directionLo := (95840170110894553109/25000000000000000000)
  directionHi := (383360680443578212437/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree060.table
  base := (-641990948358687982482218297218942229447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-70859483444994687757879028184938247250000000000)
      constant := (1118846883072149458960635889439534351779793703457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree060.table
  base := (-5135937885284582296834213556215477248353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-567023739600731787425950719738299728000000000000)
      constant := (8955483178479338539432163799914629490497666548343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95840170110894553109/25000000000000000000)
  centralHi := (383360680443578212437/100000000000000000000)
  directionLo := (24162240564187891559/6250000000000000000)
  directionHi := (77319169805401252989/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree061.table
  base := (-4829454933930659312231773201431418227169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-576312469714009296783038855098687928000000000000)
      constant := (9258038412720080069979540562266524752743606568439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree061.table
  base := (-4829463734987854723103459279133940187137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-5188165256599168382118053918356154164500000000000)
      constant := (83366142318143896798422639846604527439406361084623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24162240564187891559/6250000000000000000)
  centralHi := (77319169805401252989/20000000000000000000)
  directionLo := (77960833669134234367/20000000000000000000)
  directionHi := (97451042086417792959/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree062.table
  base := (-4500868827276885248370864175749304617837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-585749071868061091503045484717869878000000000000)
      constant := (9570615939163662034791686781477331330978947665547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree062.table
  base := (-2250438173444230345969646906395911365077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-2636558428395875338701275679533805388500000000000)
      constant := (43090393560118950097959250045315234671484650837883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77960833669134234367/20000000000000000000)
  centralHi := (97451042086417792959/25000000000000000000)
  directionLo := (196493147994026042033/50000000000000000000)
  directionHi := (392986295988052084067/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree063.table
  base := (-129693229009023314664781038208517376139/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-74398209252764110777881514292131478500000000000)
      constant := (1236063430599552050111001336719505491576490770036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree063.table
  base := (-207509487577082677702055169565472494687/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-148835234916231471463529133327196316375000000000)
      constant := (2473424478458909863495099409329631522446433639485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196493147994026042033/50000000000000000000)
  centralHi := (392986295988052084067/100000000000000000000)
  directionLo := (49517857891301038799/12500000000000000000)
  directionHi := (396142863130408310393/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree064.table
  base := (-236088140841810953016374699671732571177/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-75577784522020585117882342994529222250000000000)
      constant := (1276464095286833434165536225732814168538658302174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree064.table
  base := (-3777415738972468371537079213641958401251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-5443020057176915267971546240490524002000000000000)
      constant := (91953623128453738371741929598939667599925844257229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49517857891301038799/12500000000000000000)
  centralHi := (396142863130408310393/100000000000000000000)
  directionLo := (79854895199707310677/20000000000000000000)
  directionHi := (199637237999268276693/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree065.table
  base := (-1691279766658581137057813253903816276663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-307029439165108237831532686787707864000000000000)
      constant := (5270115875520431405254403741753856196152501163953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree065.table
  base := (-3382564216946515018614099479095765033511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-5527971657369497563256043681201980614500000000000)
      constant := (94911811569376131019814558283887916818923867189769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79854895199707310677/20000000000000000000)
  centralHi := (199637237999268276693/50000000000000000000)
  directionLo := (16095268689085223101/4000000000000000000)
  directionHi := (201190858613565288763/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree066.table
  base := (-741409878432773801108612383290135380849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-155873870121067067595768000798649419500000000000)
      constant := (2718516073213919819204939507254718868974298796519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree066.table
  base := (-1482821755924831950387019547730131470777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-311829069864559992141141173439635401500000000000)
      constant := (5439880304786702959591967726895059303012829118687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16095268689085223101/4000000000000000000)
  centralHi := (201190858613565288763/50000000000000000000)
  directionLo := (405465147125376243397/100000000000000000000)
  directionHi := (202732573562688121699/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree067.table
  base := (-1263328604580308513396061604771129913583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-316466041319160032551539316406889814000000000000)
      constant := (5606605144206660826764816765937571428977709324473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree067.table
  base := (-315832577673947542667341504440559760283/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-712234357219332769228129820328111729937500000000)
      constant := (12621465498376067733132427588200926678224154714557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405465147125376243397/100000000000000000000)
  centralHi := (202732573562688121699/50000000000000000000)
  directionLo := (408525304856567646723/100000000000000000000)
  directionHi := (102131326214141911681/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree068.table
  base := (-413123703050868174666653853608424809791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-642368684792371859823085262432961578000000000000)
      constant := (11557669654230409214071646815923216978347832926605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree068.table
  base := (-2065621426863940954241394977704100776911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-5782826457947244449109536003336350452000000000000)
      constant := (104073446322399040084706784222457091288803180478369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408525304856567646723/100000000000000000000)
  centralHi := (102131326214141911681/25000000000000000000)
  directionLo := (102890677384694352963/25000000000000000000)
  directionHi := (411562709538777411853/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree069.table
  base := (-49454012109193783316027545106680700983/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-81475660868302956817886486506517941000000000000)
      constant := (1488430290017060036499824842823130625573919015492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree069.table
  base := (-197816358930002606236723668309453627099/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-81496917474164260338806020056219542562500000000)
      constant := (1489208498088425377569099886422717909868005805269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102890677384694352963/25000000000000000000)
  centralHi := (411562709538777411853/100000000000000000000)
  directionLo := (41457786127294423339/10000000000000000000)
  directionHi := (414577861272944233391/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree070.table
  base := (-1077390991268573065079216332848465162169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-661241889100475449263098521671325478000000000000)
      constant := (12262528227148931540162169267189034191913074553439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree070.table
  base := (-1077393109959171291758816218658420396269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-5952729658332409039678530884759263677000000000000)
      constant := (110420420077412256730195659665240811316804555914851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41457786127294423339/10000000000000000000)
  centralHi := (414577861272944233391/100000000000000000000)
  directionLo := (4175712421041433791/1000000000000000000)
  directionHi := (417571242104143379101/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree071.table
  base := (-550209827958936798512923706131631556709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1766133670092873066970184950100000000000000)
      linear := (-133044731452990923226166465243108000000000000)
      constant := (2504052236795796363679388317707837996957204419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree071.table
  base := (-275105817382445512622557861369874925531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126405000000000000000000000000000000000000000
      center := (2224728)
      previous := (1112364)
      next := (1112364)
      square := (7947601515417928801365832275450000000000000)
      linear := (-598857494398431991168719334008204750000000000)
      constant := (11274119274198210809937682888946280793570150789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4175712421041433791/1000000000000000000)
  centralHi := (417571242104143379101/100000000000000000000)
  directionLo := (210271658460636139217/50000000000000000000)
  directionHi := (84108663384254455687/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree072.table
  base := (-123480110059418576404611403566670293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-85014386676072379837888972613711172250000000000)
      constant := (1623579946759334208340703344307144508245883840483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree072.table
  base := (-61836339464793224986363195660930089/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-85036567482188522642326746752530234750000000000)
      constant := (1624427261436317956624423451328573755576485149918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210271658460636139217/50000000000000000000)
  centralHi := (84108663384254455687/20000000000000000000)
  directionLo := (105873633574976478011/25000000000000000000)
  directionHi := (84698906859981182409/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree073.table
  base := (570272495699262179041126956991684401411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-689551695562630833423118410528871328000000000000)
      constant := (13359664937274077485864781563134722095468643598459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree073.table
  base := (285135591200812317315270709445689055367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-3103792229455077962766011603446816757250000000000)
      constant := (60149848332889055747967111891970394113460586193207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105873633574976478011/25000000000000000000)
  centralHi := (84698906859981182409/20000000000000000000)
  directionLo := (106606331823162219291/25000000000000000000)
  directionHi := (85285065458529775433/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree074.table
  base := (232713820351316824617199085614979978271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-698988297716682628143125040148053278000000000000)
      constant := (13736003385832333928796538444734741699119668438995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree074.table
  base := (581783991191984014468498393134065516797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-3146268029551369110408260323802545063500000000000)
      constant := (61844235892598828373747652907040517659905510728237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106606331823162219291/25000000000000000000)
  centralHi := (85285065458529775433/20000000000000000000)
  directionLo := (42933611417092697877/10000000000000000000)
  directionHi := (429336114170926978771/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree075.table
  base := (1778900228649636668188803632581420912407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-708424899870734422863131669767235228000000000000)
      constant := (14117654894988378825022465168881282520129817316783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree075.table
  base := (1778899274728587413616781974021451047901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-708609739921702279566779787590727415500000000000)
      constant := (14125009773271406697451449474760002395916630255269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42933611417092697877/10000000000000000000)
  centralHi := (429336114170926978771/100000000000000000000)
  directionLo := (432227299121815969619/100000000000000000000)
  directionHi := (21611364956090798481/5000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree076.table
  base := (302033050786149404959057869070831650961/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-89732687753098277197892287423302147250000000000)
      constant := (1813077430490687538685772630039534083898156772409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree076.table
  base := (2416263593499521438976153423280174932213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-6462439259487902811385515529028003352000000000000)
      constant := (130609545001692013481635258596891252873257296615973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432227299121815969619/100000000000000000000)
  centralHi := (21611364956090798481/5000000000000000000)
  directionLo := (435099272903194250339/100000000000000000000)
  directionHi := (21754963645159712517/5000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree077.table
  base := (615132079747802747636268043232104177187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-727298104178838012303144929005599128000000000000)
      constant := (14896897015142632264195219502224025831622869323015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree077.table
  base := (3075659706312631251222202804411105995903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-6547390859680485106670012969739459964500000000000)
      constant := (134141842754888807249409380929692705291488223088463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435099272903194250339/100000000000000000000)
  centralHi := (21754963645159712517/5000000000000000000)
  directionLo := (109488103365056526571/25000000000000000000)
  directionHi := (87590482692045221257/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree078.table
  base := (234817947931194057448888176821662667717/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-92091838291611225877893944828097634750000000000)
      constant := (1911810949240742907733643221029435131721727128346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree078.table
  base := (37570865771050986379578492576208888507/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-184231734996474094498736400290303238250000000000)
      constant := (3825610585749878338218084089736453496154656942075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109488103365056526571/25000000000000000000)
  centralHi := (87590482692045221257/20000000000000000000)
  directionLo := (17631483460237161433/4000000000000000000)
  directionHi := (220393543252964517913/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree079.table
  base := (4460543837140784832384577554664544434281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-746171308486941601743158188243963028000000000000)
      constant := (15697391167904703494524258798382662693247428353489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree079.table
  base := (4460543334844459623902666205385126071487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-6717294060065649697239007851162373189500000000000)
      constant := (141349959887006750211572753534781580961030183011727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17631483460237161433/4000000000000000000)
  centralHi := (220393543252964517913/50000000000000000000)
  directionLo := (22180182303417497917/5000000000000000000)
  directionHi := (443603646068349958341/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree080.table
  base := (1296507418735807418959013926619031983713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-188901977660248349115791204465786244500000000000)
      constant := (4026401931669493490776422573888856401505781327497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree080.table
  base := (129650731180715814880700067881269062107/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-850280707532278999065438161484228725250000000000)
      constant := (18128222382699563280530262741786323122175797723735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22180182303417497917/5000000000000000000)
  centralHi := (443603646068349958341/100000000000000000000)
  directionLo := (111600608751666994379/25000000000000000000)
  directionHi := (446402435006667977517/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree081.table
  base := (2966772031366608991033783643711977696877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-382522256397522595591585723741163464000000000000)
      constant := (8259568630750406740879825056519919759887009092213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree081.table
  base := (741692962322511178577867068776570861581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-95655517506261309552888926841462311312500000000)
      constant := (2065964424059750106170889624211703732806478192189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111600608751666994379/25000000000000000000)
  centralHi := (446402435006667977517/100000000000000000000)
  directionLo := (449183785498353622559/100000000000000000000)
  directionHi := (2807398659364710141/625000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree082.table
  base := (6703086481257322157039713763735951117487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-774481114949096985903178077101508878000000000000)
      constant := (16937979765020505761925276974939339635199354775303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree082.table
  base := (1675771542816176406704900266386983103419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-1743037215160849145773125043324185756750000000000)
      constant := (38130234558288793566080857323002304167691642660299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449183785498353622559/100000000000000000000)
  centralHi := (2807398659364710141/625000000000000000)
  directionLo := (56493502437418008857/12500000000000000000)
  directionHi := (451948019499344070857/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree083.table
  base := (1873664123480744440316728759348296053427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-195979429275787195155796176680172707000000000000)
      constant := (4340533807763706576749016198500735331416059349163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree083.table
  base := (7494656230072813731886686270055800410767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-7057100460835978878376997614008199639500000000000)
      constant := (156340278108692224129557261321789069174048696256607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56493502437418008857/12500000000000000000)
  centralHi := (451948019499344070857/100000000000000000000)
  directionLo := (14209232786844968091/3125000000000000000)
  directionHi := (454695449179038978913/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree084.table
  base := (4154126866817437052500626131103464178079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-396677159628600287671595668169936389000000000000)
      constant := (8895801827202821739248838235985163610247044735351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree084.table
  base := (4154126754544923625330688992340780057941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-396780670057142287425638614151092014000000000000)
      constant := (8900414339571136018336735771831285574087274352029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14209232786844968091/3125000000000000000)
  centralHi := (454695449179038978913/100000000000000000000)
  directionLo := (457426377331780626721/100000000000000000000)
  directionHi := (228713188665890313361/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree085.table
  base := (4571938945864362918491297638518268008139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-401395460705626185031598982979527364000000000000)
      constant := (9113192515351109415796022101398874258957541615491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree085.table
  base := (9143877700659446946372461583159488739891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-7227003661221143468945992495431112864500000000000)
      constant := (164122478204711652499378854284542679886922207414211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457426377331780626721/100000000000000000000)
  centralHi := (228713188665890313361/50000000000000000000)
  directionLo := (460141097766353706013/100000000000000000000)
  directionHi := (230070548883176853007/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree086.table
  base := (400061148346720404571248304300063704401/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-812227523565304164783204595578236678000000000000)
      constant := (18666479356269471341150922462882514377127105094225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree086.table
  base := (10001528546105312752406319509542741406429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-7311955261413725764230489936142569477000000000000)
      constant := (168085338353019735510368451755885519327907490938509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460141097766353706013/100000000000000000000)
  centralHi := (230070548883176853007/50000000000000000000)
  directionLo := (231419947837461501903/50000000000000000000)
  directionHi := (462839895674923003807/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree087.table
  base := (10881205966222624658768083266026302911749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-821664125719355959503211225197418628000000000000)
      constant := (19111886628017225878028719523638539637425557925581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree087.table
  base := (217624116558627147187156379934203537669/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-410939270089239336639721520936334782750000000000)
      constant := (9560891029415925843598369365663488979258835151525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231419947837461501903/50000000000000000000)
  centralHi := (462839895674923003807/100000000000000000000)
  directionLo := (93104609596544067187/20000000000000000000)
  directionHi := (7273797624730005249/1562500000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree088.table
  base := (11782909480893264476224234076094827565431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-831100727873407754223217854816600578000000000000)
      constant := (19562606843347101272124750489477358182352361517839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree088.table
  base := (11782909363264475567821689330083686241843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-7481858461798890354799484817565482702000000000000)
      constant := (176154578710806814845980228767431935707947245763203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93104609596544067187/20000000000000000000)
  centralHi := (7273797624730005249/1562500000000000000)
  directionLo := (234095411839847189357/50000000000000000000)
  directionHi := (93638164735938875743/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree089.table
  base := (317665977459574855666093418530920768157/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-105067166253432443617903060554472816000000000000)
      constant := (2502330000009278355355307378189989119107314692665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree089.table
  base := (2541327799668369991589271551650817797669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-7566810061991472650083982258276939314500000000000)
      constant := (180260958877384417168766012286671180716347163072745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234095411839847189357/50000000000000000000)
  centralHi := (93638164735938875743/20000000000000000000)
  directionLo := (470843484135247645169/100000000000000000000)
  directionHi := (47084348413524764517/10000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree090.table
  base := (6826197344474577616380909809828610362589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-424986966090755671831615557027482239000000000000)
      constant := (10239993048180712308401229753785988993769411517541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree090.table
  base := (109219156831010502125236503641088461533/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-850195740242672771707608855443155103000000000000)
      constant := (20490575445860324316387980421638860616469659884625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470843484135247645169/100000000000000000000)
  centralHi := (47084348413524764517/10000000000000000000)
  directionLo := (473481283397102964381/100000000000000000000)
  directionHi := (236740641698551482191/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree091.table
  base := (1827522017936919151866186889785929920911/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-107426316791945392297904717959268303500000000000)
      constant := (2618330641332983901714286126329599909221006393959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree091.table
  base := (7310088035579918509244840478524471769803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-3868356631188318620326488569849926269750000000000)
      constant := (94308619551514201789939383013605559780354318690363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473481283397102964381/100000000000000000000)
  centralHi := (236740641698551482191/50000000000000000000)
  directionLo := (238052234237633370307/50000000000000000000)
  directionHi := (95220893695053348123/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree092.table
  base := (1951247921285704145778728275955102583701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-108605892061201866637905546661666047250000000000)
      constant := (2677327137710321250912950942176810954747542805469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree092.table
  base := (7804991654393771951125153967404435184037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-3910832431284609767968737290205654576000000000000)
      constant := (96433569568296047291512167839864442693374590200277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238052234237633370307/50000000000000000000)
  centralHi := (95220893695053348123/20000000000000000000)
  directionLo := (19148531184479494357/4000000000000000000)
  directionHi := (239356639805993679463/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree093.table
  base := (2077727036522717503576339253244027048009/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-109785467330458340977906375364063791000000000000)
      constant := (2736987751040653783697911569652217617834128553521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree093.table
  base := (8310908119951682833421790813323182334753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-439256470153433435067887334506820320250000000000)
      constant := (10953604394646629871376536138578868953954479553257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19148531184479494357/4000000000000000000)
  centralHi := (239356639805993679463/50000000000000000000)
  directionLo := (120326987634635949299/25000000000000000000)
  directionHi := (481307950538543797197/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree094.table
  base := (17655674844320158046757651084894479171609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-887720340797718522543257632531692278000000000000)
      constant := (22378499849673373655523927995860081254236963441921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree094.table
  base := (17655674799884263289789864502643653927823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-7991568062954384126506469461834222377000000000000)
      constant := (201510458995934474500471552272941982979621887338783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120326987634635949299/25000000000000000000)
  centralHi := (481307950538543797197/100000000000000000000)
  directionLo := (241944354359820645033/50000000000000000000)
  directionHi := (483888708719641290067/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree095.table
  base := (4677889743039724173102094661840371306997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-224289235737942579315816065537718557000000000000)
      constant := (5716602656238669090412230248325589822167328402493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree095.table
  base := (73092027087473217404443841840175500783/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-1009564957893370802723870862818209873687500000000)
      constant := (25737984850819087904592690611162934541655501375176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241944354359820645033/50000000000000000000)
  centralHi := (483888708719641290067/100000000000000000000)
  directionLo := (121613943896534327213/25000000000000000000)
  directionHi := (486455775586137308853/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree096.table
  base := (19789468629835149108429732612950108393841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-906593545105822111983270891770056178000000000000)
      constant := (23359634333519713292046907090378133811425107119129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree096.table
  base := (4947367149435438437366796342087565371797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-226707535092765242140985120646031544500000000000)
      constant := (5842920514713095651043655609547681485463193353693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121613943896534327213/25000000000000000000)
  centralHi := (486455775586137308853/100000000000000000000)
  directionLo := (9780187335135435193/2000000000000000000)
  directionHi := (489009366756771759651/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree097.table
  base := (20889403778784328044348965306706032021943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-916030147259873906703277521389238128000000000000)
      constant := (23858170974822403373835946850115694631500124588367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree097.table
  base := (417788075030283733076866978522929523319/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-4123211431766065506179980891984296107250000000000)
      constant := (107417119080197456747385593763300862649916020704975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9780187335135435193/2000000000000000000)
  centralHi := (489009366756771759651/100000000000000000000)
  directionLo := (491549692249529786751/100000000000000000000)
  directionHi := (3840231970699451459/781250000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree098.table
  base := (11005682193289434077662053117445758570241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-462733374706962850711642075504210039000000000000)
      constant := (12181010274201783400737267346015350961687810930729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree098.table
  base := (22011364363409499381626259343225090778813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-8331374463724713307644459224680048827000000000000)
      constant := (219371177694606632104337639249371131786777503294573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491549692249529786751/100000000000000000000)
  centralHi := (3840231970699451459/781250000000000000)
  directionLo := (494076956683223564051/100000000000000000000)
  directionHi := (123519239170805891013/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree099.table
  base := (5788837606487952715546024300826933550941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-233725837891994374035822695156900507000000000000)
      constant := (6217795763469274708341402138046116360270594669029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree099.table
  base := (4631070081253710781848791894642382896583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-935147340435255066992106296154611715500000000000)
      constant := (24883995236538377489722001448927111824594749012635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494076956683223564051/100000000000000000000)
  centralHi := (123519239170805891013/25000000000000000000)
  directionLo := (124147839867460164863/25000000000000000000)
  directionHi := (496591359469840659453/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree100.table
  base := (2432136187397575916423510972203717813299/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-472169976861014645431648705123391989000000000000)
      constant := (12692829245459171826624625350951369258323121437655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree100.table
  base := (24321361857255750242339655315967555108653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-8501277664109877898213454106102962052000000000000)
      constant := (228588576460201005808023887655458910853448058581213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124147839867460164863/25000000000000000000)
  centralHi := (496591359469840659453/100000000000000000000)
  directionLo := (124773273749542672933/25000000000000000000)
  directionHi := (499093094998170691733/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree101.table
  base := (5101879742274494658722155217189411871159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-953776555876081085583304039865965928000000000000)
      constant := (25905446859254318127989952605064698682281088329355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree101.table
  base := (25509398697170992083136252669930484271779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-8586229264302460193497951546814418664500000000000)
      constant := (233269035686226567830380081290708563330690218135859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124773273749542672933/25000000000000000000)
  centralHi := (499093094998170691733/100000000000000000000)
  directionLo := (100316470561837763471/20000000000000000000)
  directionHi := (125395588202297204339/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree102.table
  base := (26719460921932315444888573604274453334941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-963213158030132880303310669485147878000000000000)
      constant := (26430548158655491046834142223962808187605378165029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree102.table
  base := (26719460909871152933044239355562533989189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-963464540499449165420272109725097253000000000000)
      constant := (26444148311651642097765660239920510516417660412941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100316470561837763471/20000000000000000000)
  centralHi := (125395588202297204339/25000000000000000000)
  directionLo := (504059317763643860849/100000000000000000000)
  directionHi := (10081186355272877217/2000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree103.table
  base := (2795154849202606196020007399547480588607/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-486324880092092337511658649552164914000000000000)
      constant := (13480481194464435149723802217183008282169472972915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree103.table
  base := (3493943560222951496915255192047745875193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-1094516558085953098008368303529666486187500000000)
      constant := (30346684226798240439464332728441495864950212713553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504059317763643860849/100000000000000000000)
  centralHi := (10081186355272877217/2000000000000000000)
  directionLo := (506524170202270432377/100000000000000000000)
  directionHi := (253262085101135216189/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree104.table
  base := (14602830705097192135440196485824136152967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-491043181169118234871661964361755889000000000000)
      constant := (13748344774956094928335758185196108678205022571423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree104.table
  base := (7301415350374301152004197078032338217039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-2210271016220051769837860967237197125500000000000)
      constant := (61899363178333936391149251714401244759065878276319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506524170202270432377/100000000000000000000)
  centralHi := (253262085101135216189/50000000000000000000)
  directionLo := (254488543049508987193/50000000000000000000)
  directionHi := (508977086099017974387/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree105.table
  base := (15240899833401319807972015864763281711801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-495761482246144132231665279171346864000000000000)
      constant := (14018864820734510774377848381218916918408711454369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree105.table
  base := (30481799659418265885071279105599151224959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-991781740563643263848437923295582790500000000000)
      constant := (28052141277832401530427562739438053222680101458071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254488543049508987193/50000000000000000000)
  centralHi := (508977086099017974387/100000000000000000000)
  directionLo := (127854559301916294257/25000000000000000000)
  directionHi := (511418237207665177029/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree106.table
  base := (635599265075011593958675544343453237761/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1584741870939511059201976207450000000000000)
      linear := (-178170090182687799783434885717671000000000000)
      constant := (5087946362314821020090101317803209694288830025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree106.table
  base := (15889981623740703422271959100923524313797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14262676838455599532817785867050000000000000)
      linear := (-1603949317419966477379928577851851500000000000)
      constant := (45815046310933724226895939328669434155842656093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127854559301916294257/25000000000000000000)
  centralHi := (511418237207665177029/100000000000000000000)
  directionLo := (513847791202165446103/100000000000000000000)
  directionHi := (64230973900270680763/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree107.table
  base := (33100152164228239358767523058504687723937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1010396168800391853903343817581057628000000000000)
      constant := (29135748615862688425480439351172715055213173265353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree107.table
  base := (33100152158906312988003435401401478603883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-9095938865457953965204936191083158339500000000000)
      constant := (262356428735473798770618541149989555459005931026043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513847791202165446103/100000000000000000000)
  centralHi := (64230973900270680763/12500000000000000000)
  directionLo := (51626591181104795773/10000000000000000000)
  directionHi := (516265911811047957731/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree108.table
  base := (34442366392510657958732303313189913494341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1019832770954443648623350447200239578000000000000)
      constant := (29692727498522026942421763496494327478175249103629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree108.table
  base := (17221183193996620404571931990816136662111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-510049470313918681138301868433034164000000000000)
      constant := (14853987065650535443547001176056062689437587656759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51626591181104795773/10000000000000000000)
  centralHi := (516265911811047957731/100000000000000000000)
  directionLo := (518672758946179163543/100000000000000000000)
  directionHi := (64834094868272395443/12500000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree109.table
  base := (35806605933785255363507665613282279033387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1029269373108495443343357076819421528000000000000)
      constant := (30255019311394533093662141333696702936567916562403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree109.table
  base := (17903302964975527049629995862992827364389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-4632921032921559277886965536253035782250000000000)
      constant := (136217472756461295330314130760009102542947217895669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518672758946179163543/100000000000000000000)
  centralHi := (64834094868272395443/12500000000000000000)
  directionLo := (104213697765234260567/20000000000000000000)
  directionHi := (130267122206542825709/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree110.table
  base := (37192870784006667544935440471697354605099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1038705975262547238063363706438603478000000000000)
      constant := (30822624054422923840896332424112082588061130101731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree110.table
  base := (37192870780752621957898777817424521242499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-9350793666035700851058428513217528177000000000000)
      constant := (277545963728599433113745427092218494548903382400979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104213697765234260567/20000000000000000000)
  centralHi := (130267122206542825709/25000000000000000000)
  directionLo := (523453254094707427509/100000000000000000000)
  directionHi := (52345325409470742751/10000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree111.table
  base := (3860116093977467342051858725152442058573/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-524071288708299516391685168028892714000000000000)
      constant := (15697770863779525739479407865160971502435507894185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree111.table
  base := (38601160937013224577360007002656898281067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1048416140692031460704769550436553865500000000000)
      constant := (31411646869812090166971708326855896366753843220323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523453254094707427509/100000000000000000000)
  centralHi := (52345325409470742751/10000000000000000000)
  directionLo := (105165440786807311051/20000000000000000000)
  directionHi := (65728400491754569407/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree112.table
  base := (20015738199115769805563089593613541476637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-528789589785325413751688482838483689000000000000)
      constant := (15986886165381225010122078128099832735997689471653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree112.table
  base := (2501967274743019112868196855784414008697/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-1190087108302608180203427924330055175250000000000)
      constant := (35988939976461026408134856985254426947974105816274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105165440786807311051/20000000000000000000)
  centralHi := (65728400491754569407/12500000000000000000)
  directionLo := (528190484173877747189/100000000000000000000)
  directionHi := (52819048417387774719/10000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree113.table
  base := (41483817156975694233365399666000557646531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1067015781724702622223383595296149328000000000000)
      constant := (32557315863999112801017863425121926683119121223739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree113.table
  base := (10370954288746873530412177766605931945963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-2401412116653361934227980208837974503625000000000)
      constant := (73291514419608249954561762552328051688054295779723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528190484173877747189/100000000000000000000)
  centralHi := (52819048417387774719/10000000000000000000)
  directionLo := (106108647479191615463/20000000000000000000)
  directionHi := (132635809348989519329/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree114.table
  base := (42958183213989132273094962082444049391159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1076452383878754416943390224915331278000000000000)
      constant := (33146172327240464529236849228878815064423158545871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree114.table
  base := (42958183212302303533733014213482730768389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1076733340756225559132935364007039403000000000000)
      constant := (33163159492031912516962501215512593177324388097741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106108647479191615463/20000000000000000000)
  centralHi := (132635809348989519329/25000000000000000000)
  directionLo := (532885603034396548159/100000000000000000000)
  directionHi := (1665267509482489213/312500000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree115.table
  base := (22227287283788184157631202346643693534147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-542944493016403105831698427267256614000000000000)
      constant := (16870170860231248422443467832659795190102728790843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree115.table
  base := (22227287283072668917651679354721588336401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-4887775833499306163740457858387405619750000000000)
      constant := (151909326530517902714597914303081327326040865605921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532885603034396548159/100000000000000000000)
  centralHi := (1665267509482489213/312500000000000000)
  directionLo := (535217717472133941653/100000000000000000000)
  directionHi := (267608858736066970827/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree116.table
  base := (11493247804078274970110532735516507646773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-273831397046714501595850871038423794500000000000)
      constant := (8584956010911260346038084316069724175068097984637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree116.table
  base := (11493247803774791995502468900704708134839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-2465125816797798655691353289371566963000000000000)
      constant := (77304177644124534708631369863408018545502455250119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535217717472133941653/100000000000000000000)
  centralHi := (267608858736066970827/50000000000000000000)
  directionLo := (134384928533399328587/25000000000000000000)
  directionHi := (537539714133597314349/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree117.table
  base := (9502686631800607361152136064110425183/2000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-138095273792613725137926264221609641000000000000)
      constant := (4368077412096394809519216037418175215126959954375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree117.table
  base := (47513433157973343594340149918593799359607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1105050540820419657561101177577524940500000000000)
      constant := (34962511997169166673512374897691377112987251893583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134384928533399328587/25000000000000000000)
  centralHi := (537539714133597314349/100000000000000000000)
  directionLo := (539851723573777293777/100000000000000000000)
  directionHi := (269925861786888646889/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree118.table
  base := (6134487549330199725823197716306100506207/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-139274849061870199477927092924007384750000000000)
      constant := (4444340934978327885015809484609950770648876668983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree118.table
  base := (24537950196884122230122874535935075513069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-5015203233788179606667204019454590538500000000000)
      constant := (160078172627490747995103858854324130411916618737949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539851723573777293777/100000000000000000000)
  centralHi := (269925861786888646889/50000000000000000000)
  directionLo := (271076936781943227807/50000000000000000000)
  directionHi := (108430774712777291123/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree119.table
  base := (25330196461192690981888471508381173409399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-561817697324506695271711686505620514000000000000)
      constant := (18085074296399746248260401894662512394770396028431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree119.table
  base := (25330196460822341911202956599585018230489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-5057679033884470754309452739810318844750000000000)
      constant := (162848961208884089691779247410016152455832809233769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271076936781943227807/50000000000000000000)
  centralHi := (108430774712777291123/20000000000000000000)
  directionLo := (544446289173757810591/100000000000000000000)
  directionHi := (17013946536679931581/3125000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree120.table
  base := (6533363842690812077504343048179328844889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-141633999600383148157928750328802872250000000000)
      constant := (4598860329459967855709435584086806171250203026241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree120.table
  base := (26133455370449174187856682297543345212129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-566683870442306877994633495574005239000000000000)
      constant := (18404852192377377304600016493023783233029087489801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544446289173757810591/100000000000000000000)
  centralHi := (17013946536679931581/3125000000000000000)
  directionLo := (546729092851133761303/100000000000000000000)
  directionHi := (68341136606391720163/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree121.table
  base := (53895453851470969268297906826953161775551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1142508598957116979983436632249604928000000000000)
      constant := (37416929608458963376509179954890830382576142228119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree121.table
  base := (13473863462734576372595619778017457114283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-2571315317038526524796975090260887728625000000000)
      constant := (84231149097495005733696178506634375999247277594443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546729092851133761303/100000000000000000000)
  centralHi := (68341136606391720163/12500000000000000000)
  directionLo := (109800480899597552181/20000000000000000000)
  directionHi := (274501202248993880453/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree122.table
  base := (1388650556293014846828159823922143327153/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-143993150138896096837930407733598359750000000000)
      constant := (4756036188891262425920404839648036226273543844285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree122.table
  base := (55546022251268930599496533332688450962663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-10370212868346688394472397801755007527000000000000)
      constant := (342609693199266710590858912763706797817878186930423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109800480899597552181/20000000000000000000)
  centralHi := (274501202248993880453/50000000000000000000)
  directionLo := (275633170772006640207/50000000000000000000)
  directionHi := (110253268308802656083/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree123.table
  base := (57218615941857665380432701002886215588789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1161381803265220569423449891487968828000000000000)
      constant := (38684962343687236164079627793690606938257686745341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree123.table
  base := (14304653985368677658437884716915160162619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-290421235237201963604358201179624003875000000000)
      constant := (9676184163627775023152094844284432000553033772611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275633170772006640207/50000000000000000000)
  centralHi := (110253268308802656083/20000000000000000000)
  directionLo := (553521019017407533843/100000000000000000000)
  directionHi := (138380254754351883461/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree124.table
  base := (29456617460766071525609770239303599711677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-585409202709636182071728260553575389000000000000)
      constant := (19663474053062708505318630330290505125225697593413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree124.table
  base := (58913234921207465950626322300502666171929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-10540116068731852985041392683177920752000000000000)
      constant := (354123406463935221119410084303234313408255879264009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553521019017407533843/100000000000000000000)
  centralHi := (138380254754351883461/25000000000000000000)
  directionLo := (555766549613070688529/100000000000000000000)
  directionHi := (55576654961307068853/10000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree125.table
  base := (30314939595225428157850123743079969852587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-590127503786662079431731575363166364000000000000)
      constant := (19987123399220245301111065931557598188002537007203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree125.table
  base := (30314939595087802998381963905148375321139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-5312533834462217640162945061944688682250000000000)
      constant := (179976011459617755352516940192471758440393880112419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555766549613070688529/100000000000000000000)
  centralHi := (55576654961307068853/10000000000000000000)
  directionLo := (111600608751666994379/20000000000000000000)
  directionHi := (69750380469791871487/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree126.table
  base := (60906785887078543245946432978882861857/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-148711451215921994197933722543189334750000000000)
      constant := (5078357302578622795075347929229620530902643050624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree126.table
  base := (62368548748135095152656631421504455294309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1190002141013001952845598618288981553000000000000)
      constant := (40647608806274407702202062336075153000782860178221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111600608751666994379/20000000000000000000)
  centralHi := (69750380469791871487/12500000000000000000)
  directionLo := (280115304838166074003/50000000000000000000)
  directionHi := (560230609676332148007/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree127.table
  base := (64129243595079643715744463387961874624873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1199128211881427748303476409964696628000000000000)
      constant := (41284782972687986403300547467281006059995013283537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree127.table
  base := (64129243594881856680626760576696043701241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-10794970869309599870894885005312290589500000000000)
      constant := (371752775475611689113913765623974088326171747627561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280115304838166074003/50000000000000000000)
  centralHi := (560230609676332148007/100000000000000000000)
  directionLo := (70306169180887781523/12500000000000000000)
  directionHi := (112489870689420450437/20000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree128.table
  base := (32955981865206515852286077454978180817723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-604282407017739771511741519791939289000000000000)
      constant := (20974010227307537336648176948284183523691515875187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree128.table
  base := (3295598186512269299006802004843561384751/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-2719980617375545541544845611505936800500000000000)
      constant := (94431227894159960180422349743827076713647668231355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70306169180887781523/12500000000000000000)
  centralHi := (112489870689420450437/20000000000000000000)
  directionLo := (282329689533270608029/50000000000000000000)
  directionHi := (564659379066541216059/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree129.table
  base := (423229432213909186650417939330786335197/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-152250177023691417217936208650382566000000000000)
      constant := (5327071358301027566676625257947949788279353365860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree129.table
  base := (13543341830816676150316487246725537149663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1218319341077196051273764431859467090500000000000)
      constant := (42638320839948443213515820022565478824103156865235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282329689533270608029/50000000000000000000)
  centralHi := (564659379066541216059/100000000000000000000)
  directionLo := (566860788503280066863/100000000000000000000)
  directionHi := (35428799281455004179/6250000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree130.table
  base := (17385869966599411884928678658428467780421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-306859504585895783115874074705560619500000000000)
      constant := (10822608552016433631154768650912441788181816251149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree130.table
  base := (34771739933138613138276306384288615068269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-5524912834943673378374188663723330213500000000000)
      constant := (194906351712142508636822563516480658600564970197149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566860788503280066863/100000000000000000000)
  centralHi := (35428799281455004179/6250000000000000000)
  directionLo := (569053681753583723507/100000000000000000000)
  directionHi := (142263420438395930877/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree131.table
  base := (8924034483353781425449083031962285439629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-154609327562204365897937866055178053500000000000)
      constant := (5496201309948276294175903635314362646170135937301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree131.table
  base := (71392275866728199760243603373643656524021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-11134777270079929052032874768158117039500000000000)
      constant := (395928359170874344394570578540762513722750934275941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569053681753583723507/100000000000000000000)
  centralHi := (142263420438395930877/25000000000000000000)
  directionLo := (114247631378870603791/20000000000000000000)
  directionHi := (142809539223588254739/25000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree132.table
  base := (14652619431088151704716279253935027883833/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1246311222651686721903509558060606378000000000000)
      constant := (44654099680968479481112280359902304695273938238885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree132.table
  base := (73263097155354279325108168590431506155793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1246636541141390149701930245429952628000000000000)
      constant := (44676872755477057476843204308951529499840569209017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114247631378870603791/20000000000000000000)
  centralHi := (142809539223588254739/25000000000000000000)
  directionLo := (28670715506715471831/5000000000000000000)
  directionHi := (573414310134309436621/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree133.table
  base := (75155943732160740272519424221264938349061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1255747824805738516623516187679788328000000000000)
      constant := (45343901812211572946809183797326753213547284751309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree133.table
  base := (75155943732087461445110491179057419428657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-11304680470465093642601869649581030264500000000000)
      constant := (408303190309533869491908540102836315318151124067297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28670715506715471831/5000000000000000000)
  centralHi := (573414310134309436621/100000000000000000000)
  directionLo := (287791117931719070721/50000000000000000000)
  directionHi := (575582235863438141443/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree134.table
  base := (77070815596933595811345318036023920731571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1265184426959790311343522817298970278000000000000)
      constant := (46039016873314689273051287743552440507601648995499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree134.table
  base := (9633851949608938239381540009729600078543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-1423704008832209492235795886286560859625000000000)
      constant := (51820295712698529207279733160717401685176551883903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287791117931719070721/50000000000000000000)
  centralHi := (575582235863438141443/100000000000000000000)
  directionLo := (577742026700761199319/100000000000000000000)
  directionHi := (14443550667519029983/2500000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree135.table
  base := (79007712749712646804644169107838637845801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1274621029113842106063529446918152228000000000000)
      constant := (46739444864277167486720478407597245710376338100369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree135.table
  base := (15801542549932008063968527417896978828979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1274953741205584248130096059000438165500000000000)
      constant := (46763264552827855557718352401863534740366948687255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577742026700761199319/100000000000000000000)
  centralHi := (14443550667519029983/2500000000000000000)
  directionLo := (579893773540509397417/100000000000000000000)
  directionHi := (289946886770254698709/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree136.table
  base := (80966635190459535895991616644742954339761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1284057631267893900783536076537334178000000000000)
      constant := (47445185785098464441167393604929954503010299179609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree136.table
  base := (20241658797603741697912925655053174425973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-2889883817760710132113840492928850025500000000000)
      constant := (106806059032779103331341845028266930065224301024933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (579893773540509397417/100000000000000000000)
  centralHi := (289946886770254698709/50000000000000000000)
  directionLo := (29101878279837889497/5000000000000000000)
  directionHi := (582037565596757789941/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree137.table
  base := (20736895729785720152740592399204169182929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-323373558355486423875885676539129032000000000000)
      constant := (12039059908944533938812633259102377377322366555001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree137.table
  base := (41473791459552561472153316677123464971909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-5822243435617711411869929706213428357250000000000)
      constant := (216813465584290701097026314577954633003161867733589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29101878279837889497/5000000000000000000)
  centralHi := (582037565596757789941/100000000000000000000)
  directionLo := (292086745223293493431/50000000000000000000)
  directionHi := (584173490446586986863/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree138.table
  base := (84950555935737142042536044064652647858061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1302930835575997490223549335775698078000000000000)
      constant := (48872606416315819793730412779575426383967631772309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree138.table
  base := (84950555935705156527927878252618626220171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1303270941269778346558261872570923703000000000000)
      constant := (48897496231982492855137277410454790530387952568899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292086745223293493431/50000000000000000000)
  centralHi := (584173490446586986863/100000000000000000000)
  directionLo := (293150817035914632957/50000000000000000000)
  directionHi := (117260326814365853183/20000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree139.table
  base := (43487777120110837069032465319098976819669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-656183718865024642471777982697440014000000000000)
      constant := (24797143063355612102506179185859232782368595564061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree139.table
  base := (21743888560048644945744992963088426360607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-2953597517905146853577213573462442484875000000000)
      constant := (111643960222224225710169725188893720121161781813247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293150817035914632957/50000000000000000000)
  centralHi := (117260326814365853183/20000000000000000000)
  directionLo := (588422080899455810269/100000000000000000000)
  directionHi := (58842208089945581027/10000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree140.table
  base := (11127822229072490605421542993428260367557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-165225504985512634957945324376757747250000000000)
      constant := (6290159845870514326151491349017403014930609237133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree140.table
  base := (89022577832556974885282811110629224919949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-11899341671813169709593351734561226552000000000000)
      constant := (453122055571742711314897818430640479189599403802429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588422080899455810269/100000000000000000000)
  centralHi := (58842208089945581027/10000000000000000000)
  directionLo := (590534913840658746067/100000000000000000000)
  directionHi := (147633728460164686517/25000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree141.table
  base := (91091626712798764931413865097025330433353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1331240642038152874383569224633243928000000000000)
      constant := (51053584337074305094255341698773294992967121716657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree141.table
  base := (22772906678194831606239770371043201259879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-332897035333493111246606921535352310125000000000)
      constant := (12769891948232727844868362398069440514254180809551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590534913840658746067/100000000000000000000)
  centralHi := (147633728460164686517/25000000000000000000)
  directionLo := (118528042865735833257/20000000000000000000)
  directionHi := (296320107164339583143/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree142.table
  base := (93182700880867924187743443310702195418511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1766133670092873066970184950100000000000000)
      linear := (-265954620946678172803724628893558000000000000)
      constant := (10273993818099910778054030702488748466930597399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree142.table
  base := (36399492531582601831925552004747602407/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 31601250000000000000000000000000000000000000
      center := (556182)
      previous := (278091)
      next := (278091)
      square := (1986900378854482200341458068862500000000000)
      linear := (-299277049994999362729675327712362125000000000)
      constant := (11564124295348196776145642858205614981476937440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118528042865735833257/20000000000000000000)
  centralHi := (296320107164339583143/50000000000000000000)
  directionLo := (594738062355429971807/100000000000000000000)
  directionHi := (18585564448607186619/3125000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree143.table
  base := (47647900168389758929201474386584408276603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-675056923173128231911791241935803914000000000000)
      constant := (26267067133433019186754220736224133652836697225907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree143.table
  base := (23823950084191393685393415050068661057057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20031929619610889543842580250271725000000000000)
      linear := (-3038549118097729148861711014173899097375000000000)
      constant := (118261934727753337104007394719993869164970593113697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594738062355429971807/100000000000000000000)
  centralHi := (18585564448607186619/3125000000000000000)
  directionLo := (298414268253480064597/50000000000000000000)
  directionHi := (119365707301392025839/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree144.table
  base := (19486185016105529797006128491442299513807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1359550448500308258543589113490789778000000000000)
      constant := (53282378626547386016342571614621512306320624766915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree144.table
  base := (97430925080515840982398810560505267376113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1359905341398166543414593499711894778000000000000)
      constant := (53309479235667918468908953027578954493435946643097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298414268253480064597/50000000000000000000)
  centralHi := (119365707301392025839/20000000000000000000)
  directionLo := (299455856998902415039/50000000000000000000)
  directionHi := (598911713997804830079/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree145.table
  base := (99588075112108074538731257401408188672791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1368987050654360053263595743109971728000000000000)
      constant := (54035935916085633078666530334291663318340606261679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree145.table
  base := (49794037556049037590215274272204142213129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-6162049836388040593007919469059254807250000000000)
      constant := (243285363606397649877996472486450791177118028429209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299455856998902415039/50000000000000000000)
  centralHi := (598911713997804830079/100000000000000000000)
  directionLo := (600987670704264032481/100000000000000000000)
  directionHi := (300493835352132016241/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree146.table
  base := (101767250431517925187334218152117797782527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1378423652808411847983602372729153678000000000000)
      constant := (54794806135480738930251865146207910812508407567063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree146.table
  base := (101767250431509457843060914822004962485039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-12409051272968663481300336378829966227000000000000)
      constant := (493403981186365089703040275460329821782203809904319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (600987670704264032481/100000000000000000000)
  centralHi := (300493835352132016241/50000000000000000000)
  directionLo := (301528240598324981643/50000000000000000000)
  directionHi := (603056481196649963287/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree147.table
  base := (6498028189922216884244843633374223489821/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-173482531870307955337951125293541953500000000000)
      constant := (6944873660591584882864987230030096078438020279498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree147.table
  base := (103968451038748300431429596363867735421313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1388222541462360641842759313282380315500000000000)
      constant := (55587230560191157874595771423498771326416203281897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301528240598324981643/50000000000000000000)
  centralHi := (603056481196649963287/100000000000000000000)
  directionLo := (605118218770542357467/100000000000000000000)
  directionHi := (151279554692635589367/25000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree148.table
  base := (4247667077352796797461069591926221239673/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1397296857116515437423615631967517578000000000000)
      constant := (56328485363841442297444411925211925201128979618425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree148.table
  base := (106191676933813849265521113411192020372393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-12578954473353828071869331260252879452000000000000)
      constant := (507214008778861197210830426982372173639070750329753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605118218770542357467/100000000000000000000)
  centralHi := (151279554692635589367/25000000000000000000)
  directionLo := (607172955477088497957/100000000000000000000)
  directionHi := (303586477738544248979/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree149.table
  base := (108436928116711260970772589876254282160519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1406733459270567232143622261586699528000000000000)
      constant := (57103294372807028441496478735040596063116634167711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree149.table
  base := (21687385623341224221350200999363982105089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-12663906073546410367153828700964336064500000000000)
      constant := (514190782397787420857546018380359782194774745001845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607172955477088497957/100000000000000000000)
  centralHi := (303586477738544248979/50000000000000000000)
  directionLo := (38076297634523968431/6250000000000000000)
  directionHi := (609220762152383494897/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree150.table
  base := (27676051146857529235709942823889210329593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-354042515356154756715907222801470369500000000000)
      constant := (14470854077907361581665709481398785443043582581217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree150.table
  base := (55352102293712882681069705468774173644167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-708269870763277370135462563426432926500000000000)
      constant := (28956410883249954142940395094518723953668000584223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38076297634523968431/6250000000000000000)
  centralHi := (609220762152383494897/100000000000000000000)
  directionLo := (611261708445964699563/100000000000000000000)
  directionHi := (152815427111491174891/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree151.table
  base := (28248376586494408172328894947136800804759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-356401665894667705395908880206265857000000000000)
      constant := (14667212795077178041005760746925128620952223444271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree151.table
  base := (56496753172986974329515473594324578812489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-6416904636965787478861411791193624644750000000000)
      constant := (264143924640498303516868472496902315074774534455769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611261708445964699563/100000000000000000000)
  centralHi := (152815427111491174891/25000000000000000000)
  directionLo := (613295862848452681841/100000000000000000000)
  directionHi := (306647931424226340921/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree152.table
  base := (57652416696177688482234879606121534696747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-717521632866361308151821075222122689000000000000)
      constant := (29729799489422424083701336482979398343845301270243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree152.table
  base := (7206552087022016138508446323257518076167/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-1614845109265519656625915127887338237750000000000)
      constant := (66926017818159990064692752511201650807123432660014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613295862848452681841/100000000000000000000)
  centralHi := (306647931424226340921/50000000000000000000)
  directionLo := (615323292718369806407/100000000000000000000)
  directionHi := (76915411589796225801/12500000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree153.table
  base := (29409546431641315273912553540798703594599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-361119966971693602755912195015856832000000000000)
      constant := (15063914926809470350379997127813254626067929327231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree153.table
  base := (58819092863281310502899611490922718679641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-722428470795374419349545470211675695250000000000)
      constant := (30143126427297186700034955162892459500732235919329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615323292718369806407/100000000000000000000)
  centralHi := (76915411589796225801/12500000000000000000)
  directionLo := (308672032154083058889/50000000000000000000)
  directionHi := (617344064308166117779/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree154.table
  base := (3749798854644045968140771908916936427499/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-181739558755103275717956926210326159750000000000)
      constant := (7632129170685980352381887319662525333602568349324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree154.table
  base := (119993563348607236181012448123732125915571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-13088664074509321843576315904521619127000000000000)
      constant := (549792248719205207546400325939488303145306385823491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308672032154083058889/50000000000000000000)
  centralHi := (617344064308166117779/100000000000000000000)
  directionLo := (309679121394740492083/50000000000000000000)
  directionHi := (619358242789480984167/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree155.table
  base := (30592741564622602572566640614344857909049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-365838268048719500115915509825447807000000000000)
      constant := (15465929988398691614099721918008386995710620469281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree155.table
  base := (122370966258488518643081744878030353379583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-13173615674701904138860813345233075739500000000000)
      constant := (557056061628847769113551038939758276921439672865743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309679121394740492083/50000000000000000000)
  centralHi := (619358242789480984167/100000000000000000000)
  directionLo := (621365892277667751181/100000000000000000000)
  directionHi := (310682946138833875591/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree156.table
  base := (124770394456210653083520982843136227541069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1472789674348929795183668668920973178000000000000)
      constant := (62675719471558688762655937969773064590003991480661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree156.table
  base := (124770394456209051964324754616424159553801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1473174141654942937127256753993836928000000000000)
      constant := (62707523824475263839607456182712681411714786752369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621365892277667751181/100000000000000000000)
  centralHi := (310682946138833875591/50000000000000000000)
  directionLo := (24934683034224300617/4000000000000000000)
  directionHi := (311683537927803757713/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree157.table
  base := (1589898099272161304011630693171350141899/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-185278284562872698737959412317519391000000000000)
      constant := (7936628989922456005065796088293652460268388209310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree157.table
  base := (127191847941771549164684116439632379875197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-13343518875087068729429808226655988964500000000000)
      constant := (571727207093494369626536519313205551078723020854637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24934683034224300617/4000000000000000000)
  centralHi := (311683537927803757713/50000000000000000000)
  directionLo := (156340463899209260453/25000000000000000000)
  directionHi := (625361855596837041813/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree158.table
  base := (64817663357589983505975102108657065727629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-745831439328516692311840964079668539000000000000)
      constant := (32157828648528841990548887225259221550747334609301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree158.table
  base := (12963532671517882008044185737349436325577/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-6714235237639825512357152833683722788500000000000)
      constant := (289567269824249556206784411227634302484152170413085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156340463899209260453/25000000000000000000)
  centralHi := (625361855596837041813/100000000000000000000)
  directionLo := (313675146294007407013/50000000000000000000)
  directionHi := (627350292588014814027/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree159.table
  base := (412815096176358484146386764548236199167/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (396185467734877764800494051862500000000000)
      linear := (-66798659701454484662855489399186500000000000)
      constant := (2898878408890745695863419101094802815950033880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree159.table
  base := (132100830776433744264408267419126018412379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3169483741879022118403952414900000000000000)
      linear := (-534528779536894637079182117324429500000000000)
      constant := (23202789133550570384563662760681800461941802539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313675146294007407013/50000000000000000000)
  centralHi := (627350292588014814027/100000000000000000000)
  directionLo := (629332446950748222147/100000000000000000000)
  directionHi := (157333111737687055537/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree160.table
  base := (67294180062770034988701228703797782564967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-755268041482568487031847593698850489000000000000)
      constant := (32988423420992574652163037833594976782945186199423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree160.table
  base := (336470900313848121315333030134139918259/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10015964809805444771921290125135862500000000000)
      linear := (-1699796709458101951910412568598794850250000000000)
      constant := (74261590550484164382419079860942523862987131596950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629332446950748222147/100000000000000000000)
  centralHi := (157333111737687055537/25000000000000000000)
  directionLo := (631308377862803952509/100000000000000000000)
  directionHi := (63130837786280395251/10000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree161.table
  base := (34274478690624745878199721061895865278327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-379993171279797192195925454254220732000000000000)
      constant := (16703852752308665463337700345991908656929842357263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree161.table
  base := (13709791476249828836293351267936926325757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40063859239221779087685160500543450000000000000)
      linear := (-6841662637928698955283898994750907707250000000000)
      constant := (300821788302121762284119115748945972658323630281985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631308377862803952509/100000000000000000000)
  centralHi := (63130837786280395251/10000000000000000000)
  directionLo := (633278143578722749801/100000000000000000000)
  directionHi := (316639071789361374901/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree162.table
  base := (17453686835914302612158582231177579309889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-191176160909155070437963555829508109750000000000)
      constant := (8457411013292677114321956752677267059038931611241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree162.table
  base := (139629494687313832652131607093294482301561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1529808541783331133983588381134808003000000000000)
      constant := (67693585409600330753005818884903674636220112723809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633278143578722749801/100000000000000000000)
  centralHi := (316639071789361374901/50000000000000000000)
  directionLo := (317620900724929434033/50000000000000000000)
  directionHi := (635241801449858868067/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree163.table
  base := (35545774974997337209359155507305665158169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-384711472356823089555928769063811707000000000000)
      constant := (17127119533326364124266953696894065142734584770561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree163.table
  base := (142183099899988851075460609647095703319467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-13853228476242562501136792870924728639500000000000)
      constant := (616888800650352050146552008295306569225925748389307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317620900724929434033/50000000000000000000)
  centralHi := (635241801449858868067/100000000000000000000)
  directionLo := (79649925992982964157/12500000000000000000)
  directionHi := (637199407943863713257/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree164.table
  base := (7237936520026336250606420900098050111733/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2225769957734543282649175583363525000000000000)
      linear := (-387070622895336038235930426468607194500000000000)
      constant := (17340745272531705620514825620894842041263040814385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree164.table
  base := (144758730400526303831138547066782948486987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-13938180076435144796421290311636185252000000000000)
      constant := (624583172496091121928900513306993805303796271987227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79649925992982964157/12500000000000000000)
  centralHi := (637199407943863713257/100000000000000000000)
  directionLo := (639151018663632403499/100000000000000000000)
  directionHi := (1278302037327264807/200000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree165.table
  base := (14735638618892948962899584156926556597303/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-778859546867697973831864167746805364000000000000)
      constant := (35111398488402778251693680815566014604404377121035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree165.table
  base := (29471277237785826652039501455715749682057/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1558125741847525232411754194705293540500000000000)
      constant := (70258376024846729677834923888257590560501241938165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639151018663632403499/100000000000000000000)
  centralHi := (1278302037327264807/200000000000000000)
  directionLo := (320548344182865616053/50000000000000000000)
  directionHi := (641096688365731232107/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree166.table
  base := (2343376051018758728006067074958319579241/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1112884978867271641324587791681762500000000000)
      linear := (-195894461986180967797966870639099084750000000000)
      constant := (8885990724167712481343795946277523960334491613832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree166.table
  base := (149976067265200257073414043213042382809849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-14108083276820309386990285193059098477000000000000)
      constant := (640115435832940757498892615353887580436313910340329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320548344182865616053/50000000000000000000)
  centralHi := (641096688365731232107/100000000000000000000)
  directionLo := (321518235489161655453/50000000000000000000)
  directionHi := (643036470978323310907/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree167.table
  base := (76308886814671409008716797964081300484601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-788296149021749768551870797365987314000000000000)
      constant := (35979183769867646696013141874356442879476732057569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree167.table
  base := (30523554725868512583085397094460237683053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-14193034877012891682274782633770555089500000000000)
      constant := (647953327324052061129860294453298055107702076218065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321518235489161655453/50000000000000000000)
  centralHi := (643036470978323310907/100000000000000000000)
  directionLo := (128994083923721799193/20000000000000000000)
  directionHi := (322485209809304497983/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree168.table
  base := (155281505281359119867772446868934162226733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1586028900197551331823748224351156578000000000000)
      constant := (72834122215986377511502244275933362391003955597877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree168.table
  base := (3105630105627178080897256692297919030109/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4451539915469086565298351166727050000000000000)
      linear := (-793221470955859665419960004137889539000000000000)
      constant := (36435503260941935645390917771924307022366488210525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell186.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128994083923721799193/20000000000000000000)
  centralHi := (322485209809304497983/50000000000000000000)
  directionLo := (646898586609797052491/100000000000000000000)
  directionHi := (161724646652449263123/25000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree169.table
  base := (157967262221252278530102429472032706163209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8903079830938173130596702333454100000000000000)
      linear := (-1595465502351603126543754853970338528000000000000)
      constant := (73715189822094992061369518291123072293548381022321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree169.table
  base := (6318690488850083837791645251157054620291/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80127718478443558175370321001086900000000000000)
      linear := (-14362938077398056272843777515193468314500000000000)
      constant := (663772629951649457769866023685596729800952187565275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell186.Kernel169
