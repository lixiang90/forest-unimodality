import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell103.Parameters
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch000_049
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_207.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_207.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel000
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
  base := (448493303310990811552549931/12500000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (312162250399701558800646950000000000000)
      linear := (-10797912596316784367839192250000000000)
      constant := (89698660662198162310509986200000000000000) }

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
  base := (448493303310990811552549931/12500000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (312162250399701558800646950000000000000)
      linear := (-10797912596316784367839192250000000000)
      constant := (89698660662198162310509986200000000000000) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel001
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
  base := (101999264904719501999259887670497907536183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-33654480984464226460642134231739840500000000000)
      constant := (5160896542369428647211624473109638324555550893167) }

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
  base := (101911980779798418514423693563690065502507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-28581686250091115090257200279640500000000000)
      constant := (4374452681575426442131884599909946116716922443) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel002
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
  base := (120191705991267467039006796796270373735609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-132436337475496425011083053242349081000000000000)
      constant := (6140323031112876066628608369963845569409682269441) }

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
  base := (60001880202775264193725895913657616056967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-56238012986503074393759317461840500000000000)
      constant := (2600568781511710042438482850525296190424978983) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel003
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
  base := (36924349384311527094238217785264935039453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-10975761832336910950048991001178804500000000000)
      constant := (215819800209997046127642930295215712845951587933) }

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
  base := (9211779223734928724023697345326420624883/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11902500000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (1486204474152979121449880128950000000000000)
      linear := (-4660796651273057427625635258002250000000000)
      constant := (91368228361928781275850009809129927190135926) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel004
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
  base := (47423259367024589323456172767484925078659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-262691088488632369190680622800087881000000000000)
      constant := (2668841845124100118561589176175723755529347748891) }

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
  base := (1892300022751307555332318996896197982529/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-223101332918653986001527103652481000000000000)
      constant := (2259638218038178284661626585311653683834628025) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel005
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
  base := (1981772629109450506117466317346222728179/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-81954615998800085320119851894739320250000000000)
      constant := (506884389765724297624272760152310807051392253484) }

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
  base := (15812061353647335727751707114312402476667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-139206993195738952304265669008440500000000000)
      constant := (858619926844702050503495947360124633722704283) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel006
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
  base := (10925711336045155183920117779528436349961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-21830324416764906298348788464323704500000000000)
      constant := (95319010655350822082114571703007978374233475721) }

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
  base := (5447461596205454320481335449077765214623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11902500000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (1486204474152979121449880128950000000000000)
      linear := (-9270184440675050644875988121702250000000000)
      constant := (40390589056236114244621579308022740186820103) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel007
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
  base := (305622958606809886995050367233704826137/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-229036607504168142730038488568348040500000000000)
      constant := (801790568880729513443978970481480289670516712825) }

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
  base := (15234984945901821193146054044179683298387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-389039293337125741822539806745681000000000000)
      constant := (1359993771543562005854973795662922249652584563) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel008
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
  base := (2655635901978913179925300042449914775649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-130800147628726064387468940478891370250000000000)
      constant := (405401048973056938185240324307176942414989607401) }

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
  base := (10586655824480880147156841215053455725997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-444351946809949660429544041110081000000000000)
      constant := (1376210905173750373605751512057273524403245453) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel009
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
  base := (3565196565168700530447244874553252121457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-32684887001192901646648585927468604500000000000)
      constant := (96231715979225017540818479804676913229208238577) }

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
  base := (177534886168806504533895658280185517797/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (9522)
      previous := (4761)
      next := (4761)
      square := (165133830461442124605542236550000000000000)
      linear := (-1542174692230782651347371220600250000000000)
      constant := (4539678815558705162022167214979431389146130) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel010
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
  base := (1098188690948468030655824571692442676039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-163363835382010050432368332868326070250000000000)
      constant := (478618565741996157843702755875244948280815392511) }

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
  base := (873701453948532297798177056301933015103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-554977253755597497643552509838881000000000000)
      constant := (1626330928575509379103744026413217638820742235) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel011
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
  base := (2175421294811588161526756242634233423201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-718582717034608173819272116252173681000000000000)
      constant := (2156684644613659962730275529644970042243266326249) }

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
  base := (53864994558523994001125287350887147319/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-152572476807105354062639186050820250000000000)
      constant := (458158822329404131967879585934129383754718310) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel012
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
  base := (6801591575021034622014541419845303297/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-43539449585620896994948383390613504500000000000)
      constant := (136211995102104332785627513431761089929914870425) }

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
  base := (321867674458000641388774267614190321633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (342792)
      previous := (171396)
      next := (171396)
      square := (5944817896611916485799520515800000000000000)
      linear := (-73955840077916148317506775396409000000000000)
      constant := (231540466526147971546806905945419160121294713) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel013
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
  base := (-149868009154631606206440154171757133651/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-212209367011936029499717421452478120250000000000)
      constant := (698885183455765583633416363874236526759937263402) }

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
  base := (-1215057671302236704291361064433795489553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-720915214174069253464565212932081000000000000)
      constant := (2376359696941852930394927808797429297068143503) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel014
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
  base := (-2497698578394224847904501563969164373779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-913964843554312090088668470588781881000000000000)
      constant := (3185028110642298267988497737726405013489992662229) }

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
  base := (-4019274657089641679603962918584335407/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-776227867646893172071569447296481000000000000)
      constant := (2707727792921572247403647089186821382590910625) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel015
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
  base := (-3594977689673717581788578341365342637797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (404075592)
      previous := (202037796)
      next := (202037796)
      square := (7007619229461757999760790350235800000000000000)
      linear := (-108788024340097784686496361707516809000000000000)
      constant := (402035399023252760294400630156418434796518550683) }

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
  base := (-1803895239227132649972291936547680358073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (2972408948305958242899760257900000000000000)
      linear := (-46196695617762060593254093425604500000000000)
      constant := (170906144894334846978789832181413993815214447) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel016
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
  base := (-180762761916130841289422047501771349123/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-1044219594567448034268266040146520681000000000000)
      constant := (4093983382372273008164853551056325261795265919325) }

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
  base := (-4530518299557243642407058296196375943263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-886853174592541009285577916025281000000000000)
      constant := (3480898550554415718641762753174777487207123713) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel017
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
  base := (-2645759168816686885061613093530679000849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-554673485037008003179032412462695040500000000000)
      constant := (2305467111738159887069202972506171946321246477799) }

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
  base := (-5301742185638667101463758666144299789139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-942165828065364927892582150389681000000000000)
      constant := (3920569849961152262038031394932059898335182989) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel018
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
  base := (-1482323592177489044151235540554597414769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14030402500000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (1751904807365439499940197587558950000000000000)
      linear := (-32624287377238443845773989158451652250000000000)
      constant := (143564278591275317281273547912529104268132594191) }

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
  base := (-5938410887391941148174543300338156184503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (38088)
      previous := (19044)
      next := (19044)
      square := (660535321845768498422168946200000000000000)
      linear := (-12314549154792454895056622034001000000000000)
      constant := (54254299620984878330587395499939115378397913) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel019
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
  base := (-6446086225036407641066328331047860516567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-1239601721087151950537662394483128881000000000000)
      constant := (5765431371715772984836864310251315324179345458417) }

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
  base := (-3227100292239208807200924094647038800943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-526395567505506382553295309559240500000000000)
      constant := (2451198898973987551108466077553088534418393393) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel020
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
  base := (-6853120165746412918318629496994226978341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-1304729096593719922627461179261998281000000000000)
      constant := (6401719218602730827966239627187053809143061155891) }

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
  base := (-1372065652272723137382102589540839843213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-1108103788483836683713594853482881000000000000)
      constant := (5443487799338389102722404141115442767790830815) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel021
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
  base := (-7159703404263669196259499851238035517161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (404075592)
      previous := (202037796)
      next := (202037796)
      square := (7007619229461757999760790350235800000000000000)
      linear := (-152206274677809766079695551560096409000000000000)
      constant := (786300829747225400334490410452132571853974205079) }

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
  base := (-3583046811218074625189845516338509630159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (2972408948305958242899760257900000000000000)
      linear := (-64634246775370033462255504880404500000000000)
      constant := (334303877246537190552743219279956855650813001) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel022
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
  base := (-368680334265937070593116156496690540797/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-358745961901713966701764687204934270250000000000)
      constant := (1947500905762001455386035292679751729054157545735) }

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
  base := (-7379260736191005819292906422505565801203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-1218729095429484520927603322211681000000000000)
      constant := (6624011088674874363889749053931641010984252653) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel023
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
  base := (-1500269432132901313390895164703228816399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (6874632)
      previous := (3437316)
      next := (3437316)
      square := (119222255321655618143378285731800000000000000)
      linear := (-2835749003995130130239806301698689000000000000)
      constant := (16146084133889556298753023208864064546907035405) }

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
  base := (-1876585120838375154381841547042031422529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (1458)
      previous := (729)
      next := (729)
      square := (25285142282375826262852402950000000000000)
      linear := (-602099125190126861783841000272250000000000)
      constant := (3432340599868527822549906907376345454775151) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel024
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
  base := (-1887101547064592241323370097616820006131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14030402500000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (1751904807365439499940197587558950000000000000)
      linear := (-43478849961666439194073786621596552250000000000)
      constant := (259173757185931575767944914594343868817571840909) }

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
  base := (-3776404095534111523119223275105044398039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (2972408948305958242899760257900000000000000)
      linear := (-73853022354174019896756210607804500000000000)
      constant := (440761113338091246920935173199732883620936321) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel025
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
  base := (-1503880442483941949898308578465222313837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-1630365974126559783076455103156345281000000000000)
      constant := (10156700603568081036826811165598084738827940270935) }

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
  base := (-1880819118957270519446995679076785485819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-346166763961989069187154006326220250000000000)
      constant := (2159103858740559893629176770469620068718141669) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel026
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
  base := (-741823098016383830421131099702621042233/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-847746674816563877583126943967607340500000000000)
      constant := (5510208884708010768999446306752873427005027201915) }

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
  base := (-7421635477696582005618890528459648710087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-1439979709320780195355620259669281000000000000)
      constant := (9370812205340143713865489407944338512421482137) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel027
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
  base := (-7248180939487931168120895234306021080241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (404075592)
      previous := (202037796)
      next := (202037796)
      square := (7007619229461757999760790350235800000000000000)
      linear := (-195624525015521747472894741412676009000000000000)
      constant := (1324582295393439521182045312487908741928293589199) }

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
  base := (-3625584147036402461663348828327560575411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (19044)
      previous := (9522)
      next := (9522)
      square := (330267660922884249211084473100000000000000)
      linear := (-9230199770330889592361879592800500000000000)
      constant := (62572528850486253376510526732478220455607581) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel028
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
  base := (-1402405826026913545456105347869127642753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-1825748100646263699345851457492953481000000000000)
      constant := (12859029004195634708116696206803789111269385634515) }

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
  base := (-1402929381097164739764345780030146951883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-1550605016266428032569628728398081000000000000)
      constant := (10934109063684480179587265342706509166293826665) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel029
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
  base := (-1678030340138049499155516847292864688671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-472718869038207917858912560567955720250000000000)
      constant := (3458416080221966958818876920197717272068671247721) }

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
  base := (-6714412379470003889648455167526052161049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-1605917669739251951176632962762481000000000000)
      constant := (11762790062654485081867946410117725190951211399) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel030
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
  base := (-6350439511814445476770874484842556379527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (404075592)
      previous := (202037796)
      next := (202037796)
      square := (7007619229461757999760790350235800000000000000)
      linear := (-217333650184377738169494336338965809000000000000)
      constant := (1649449611655182535629422697960866408946517372153) }

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
  base := (-6352442191058415925128856059814539394867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (342792)
      previous := (171396)
      next := (171396)
      square := (5944817896611916485799520515800000000000000)
      linear := (-184581147023563985531515244125209000000000000)
      constant := (1402523104206788413223414558774492977941038213) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel031
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
  base := (-296432908844297029858973043266995516487/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-505282556791491903903811952957390420250000000000)
      constant := (3973272743363504226201076553553054976258856071685) }

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
  base := (-741300858578928220640553349638143538817/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-429135744171224947097660357872820250000000000)
      constant := (3378447777208435447500378497644763125010460734) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel032
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
  base := (-5448192400220396351733088945170670619117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-2086257602672535587705046596608431081000000000000)
      constant := (16977726253444322538368728504706970008067911463467) }

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
  base := (-1362429432892403582315007492913567552191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-442963907539430926749411416463920250000000000)
      constant := (3608994775487071195753822389431994543956167841) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel033
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
  base := (-2455118977938684047731445372323707976411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-119521387676616864433046965632627804500000000000)
      constant := (1005493997054371282621691627607766823969397265829) }

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
  base := (-4911567159691687215723989924614968777453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (342792)
      previous := (171396)
      next := (171396)
      square := (5944817896611916485799520515800000000000000)
      linear := (-203018698181171958400516655580009000000000000)
      constant := (1709913424991319220208365135635905133650546267) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel034
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
  base := (-863161070281752752642673977944779203573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-2216512353685671531884644166166169881000000000000)
      constant := (19256537013877441342581744812085292379004344693615) }

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
  base := (-2158481291738586220584116181096394915501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-941240468551685772105827067292240500000000000)
      constant := (8186736555182944545297992807489677574265697651) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel035
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
  base := (-3665748546004683852860671073910846176949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-2281639729192239503974442950945039281000000000000)
      constant := (20450618321132436842140265311429937531978549508899) }

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
  base := (-3666755185102920208537039530661750546313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-1937793590576195462818658368948881000000000000)
      constant := (17388699485975237254831428190526009650841034263) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel036
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
  base := (-2960789210430159871046824769124869411199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (404075592)
      previous := (202037796)
      next := (202037796)
      square := (7007619229461757999760790350235800000000000000)
      linear := (-260751900522089719562693526191545409000000000000)
      constant := (2409011046394552048444209110621780077760376008961) }

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
  base := (-1480832069551162726967458148024565860527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (19044)
      previous := (9522)
      next := (9522)
      square := (330267660922884249211084473100000000000000)
      linear := (-12303124963265551737195448168600500000000000)
      constant := (113795488492841580462743654434313004659781217) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel037
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
  base := (-440307444791956444217169266959390552493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-2411894480205375448154040520502778081000000000000)
      constant := (22947949498466920043182516174801145773588864968215) }

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
  base := (-2202297088871475355084722170874157969499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-2048418897521843300032666837677681000000000000)
      constant := (19511956023049306491516870291225510205164937349) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel038
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
  base := (-694253996821571521455112685351977641341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-1238510927855971710121919652640823740500000000000)
      constant := (12125571265477103024515723451081176539775546468891) }

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
  base := (-694583722569284328864449926816510900637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-1051865775497333609319835536021040500000000000)
      constant := (10309969074232928018216152540969278324418605187) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel039
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
  base := (-261068544705462460953037276614203600351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-141230512845472855129646560558917604500000000000)
      constant := (1421703139700868150442384787452424761258050531489) }

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
  base := (-8167328132671446661627220596465253221/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 11902500000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (1486204474152979121449880128950000000000000)
      linear := (-59973450124096976034629869622402250000000000)
      constant := (604411025680872460319699293939756412870637104) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel040
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
  base := (15888295540934744624215805505899474361/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-2607276606725079364423436874839386281000000000000)
      constant := (26966472856912221174502912627133372457484093427225) }

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
  base := (198355861581948178102909113328082093633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-1107178428970157527926839770385440500000000000)
      constant := (11464258323044376603508135351888614989630080417) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel041
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
  base := (273842871668436001393191008176897333483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-2672403982231647336513235659618255681000000000000)
      constant := (28378575845272790697635756156146433552718977904335) }

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
  base := (684392521144803892170823447592663270427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-1134834755706569487230341887567640500000000000)
      constant := (12064542021784018718680952276484908528474526523) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel042
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
  base := (1196810462197965060463785101261218072931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-152085075429900850477946358022062504500000000000)
      constant := (1657052900054607252131123324073642285381398513891) }

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
  base := (1196624648694319128843138248310846599897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (2972408948305958242899760257900000000000000)
      linear := (-129165675826997938503760444972204500000000000)
      constant := (1408915994727858437813853287154496940662109617) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel043
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
  base := (3470204913174072685853147094589468021619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-2802658733244783280692833229175994481000000000000)
      constant := (31311590702181040608806909736611430106475095777931) }

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
  base := (433735425705517595328660737003542246203/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-595073704589696702918673060966020250000000000)
      constant := (6655679689377844364798110403999925313415104694) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel044
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
  base := (36790228523932860536644077210220464139/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-2867786108751351252782632013954863881000000000000)
      constant := (32832481865254141863109113551779089415523143676375) }

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
  base := (183940022740116552126009086081891362833/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-2435607471831610730281696478228481000000000000)
      constant := (27915768596666608042088171720786838075150780425) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel045
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
  base := (288959160288422729275251978034261387853/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14030402500000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (1751904807365439499940197587558950000000000000)
      linear := (-81469819007164422913123077742603702250000000000)
      constant := (955267157655169852667900991514974590248572401665) }

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
  base := (361183934692004583206947660050578288223/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (9522)
      previous := (4761)
      next := (4761)
      square := (165133830461442124605542236550000000000000)
      linear := (-7688025078100106941014508372200250000000000)
      constant := (90245773640960538397427335773053273657879868) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel046
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
  base := (3505642368519022013886141393029397657517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 477405000000000000000000000000000000000000000
      center := (3437316)
      previous := (1718658)
      next := (1718658)
      square := (59611127660827809071689142865900000000000000)
      linear := (-2833687013009912284463354993868244500000000000)
      constant := (34010388809086072873318766304157999417737380677) }

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
  base := (3505538604996380460627652300336076285299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (2916)
      previous := (1458)
      next := (1458)
      square := (50570284564751652525704805900000000000000)
      linear := (-2406647238919904128067774051944500000000000)
      constant := (28917107024935184244364611849274222179109219) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel047
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
  base := (4147484916887166472735147091699076096879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-1531584117635527584526014184145736040500000000000)
      constant := (18806298597262557505207473971658826342212428909671) }

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
  base := (8294790657929300591030161126249906316921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-2601545432250082486102709181321681000000000000)
      constant := (31979769486771781131251397023037789235773747929) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel048
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
  base := (192602854488863737705516396287256927501/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-173794200598756841174545952948352304500000000000)
      constant := (2182135018986380300635902305543438719137523491525) }

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
  base := (2407497024160924502491068578788727292963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11902500000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (1486204474152979121449880128950000000000000)
      linear := (-73801613492302955686380928213502250000000000)
      constant := (927667703986710756217567459826521130641796843) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel049
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
  base := (11016722472429475570330455448010561711447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-3193422986284191113231625937849210881000000000000)
      constant := (40980486713638422147717799970467731024725684962703) }

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
  base := (11016589087379815410269358234196680676323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-2712170739195730323316717650050481000000000000)
      constant := (34843099355910581461068893664731762570299764227) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel050
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
  base := (6227320339070945703546746456140118741717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-1629275180895379542660712361314040140500000000000)
      constant := (21359381427675088223745183113267276776938698983933) }

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
  base := (12454525665436929825589491685801530959343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-2767483392668554241923721884414881000000000000)
      constant := (36320952611719302564575407488573959800076888207) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel051
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
  base := (3485959884263943027030671722777715877383/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14030402500000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (1751904807365439499940197587558950000000000000)
      linear := (-92324381591592418261422875205748602250000000000)
      constant := (1235923773533761608658726467715147001591129654663) }

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
  base := (6971870202886082293065993835038995295021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (2972408948305958242899760257900000000000000)
      linear := (-156822002563409897807262562154404500000000000)
      constant := (2101644147241227128440445732223500156599594981) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel052
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
  base := (15484270198559921271249377269391732302753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-3388805112803895029501022292185819081000000000000)
      constant := (46303963221816691696884838376617428125767555213097) }

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
  base := (1548418478857617768047736827896895395439/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-1439054349807101039568865176571840500000000000)
      constant := (19684511696376814103639713765098276353995828555) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel053
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
  base := (8537945689506826476411570920480890513981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-1726966244155231500795410538482344240500000000000)
      constant := (24075441446970027021003297484450201035140507106469) }

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
  base := (17075817818304258201259969222123600868459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-2933421353087025997744734587508081000000000000)
      constant := (40939237082335826932959909189917367173612599691) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel054
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
  base := (18718668189637591512891913318559364486379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (404075592)
      previous := (202037796)
      next := (202037796)
      square := (7007619229461757999760790350235800000000000000)
      linear := (-391006651535225663742291095749284209000000000000)
      constant := (5559334789041386933437935701055967052555241255019) }

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
  base := (1871860485685870542514022515550815101773/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (19044)
      previous := (9522)
      next := (9522)
      square := (330267660922884249211084473100000000000000)
      linear := (-18448975349134876026862585320200500000000000)
      constant := (262594038486918741423920315578758905944189585) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel055
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
  base := (10206285572980544003196156953189221258187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-1792093619661799472885209323261213640500000000000)
      constant := (25976676177434805119400867457941167367240112108963) }

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
  base := (20412516637713400624122500756708617637097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-3044046660032673834958743056236881000000000000)
      constant := (44172013596347278079049088353791162557131969353) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel056
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
  base := (22157575330703658121691911798092428041761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-3649314614830166917860217431301296681000000000000)
      constant := (53908899395873329714553837366968665227461497099689) }

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
  base := (22157528432921324929461599012091466448729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-3099359313505497753565747290601281000000000000)
      constant := (45834574107167351026575037933176843245861588921) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel057
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
  base := (11976829843161979013731692761838957355031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-206357888352040827219445345337787004500000000000)
      constant := (3105591842265490569808768706481441259998568131991) }

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
  base := (23953619349297010163143697853169346666581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (342792)
      previous := (171396)
      next := (171396)
      square := (5944817896611916485799520515800000000000000)
      linear := (-350519107442035741352527947218409000000000000)
      constant := (5280879430232105647477025066678152259479592141) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel058
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
  base := (2580080641715117306382968350121268276561/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-1889784682921651431019907500429517740500000000000)
      constant := (28964306375368292215481110340913348705651378624445) }

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
  base := (5160154346748476165452383942521758279429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-3209984620451145590779755759330081000000000000)
      constant := (49252035134694478044193839557688072102576266105) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel059
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
  base := (27699000484124819612167945416070184011389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-3844696741349870834129613785637904881000000000000)
      constant := (59992777406131933732516822449155175831243868114661) }

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
  base := (27698970670790794059111377504716003374719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-3265297273923969509386759993694481000000000000)
      constant := (51006934255871102497252838099196055028603334431) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel060
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
  base := (29648229177798181296411271065716651700789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (404075592)
      previous := (202037796)
      next := (202037796)
      square := (7007619229461757999760790350235800000000000000)
      linear := (-434424901872937645135490285601863809000000000000)
      constant := (6899238498335303046911914011364823219725751695029) }

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
  base := (29648203558068722015625525523592763783787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (342792)
      previous := (171396)
      next := (171396)
      square := (5944817896611916485799520515800000000000000)
      linear := (-368956658599643714221529358673209000000000000)
      constant := (5865845743957746765769184756408365148374609907) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel061
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
  base := (15824240878741281515915213231159461891161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-1987475746181503389154605677597821840500000000000)
      constant := (32114859722443848815387374859146935565509040080289) }

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
  base := (31648459747592148672952389761769645141631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-3375922580869617346600768462423281000000000000)
      constant := (54609066997684866125597280448879708524673746719) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel062
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
  base := (8424937286571833421716990700683924902461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-1010019716967393687599752534993628270250000000000)
      constant := (16600623956818274986625545011573546431730683853989) }

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
  base := (2106233140168030428920347649550826069673/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-857808808585610316301943174196920250000000000)
      constant := (14114074944142028627674839703463618885037673508) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel063
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
  base := (4475252959174706502872902059589492176821/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14030402500000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (1751904807365439499940197587558950000000000000)
      linear := (-114033506760448408958022470132038402250000000000)
      constant := (1905874312353480648816898627867672830384119840362) }

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
  base := (17901003720958995081654431616171787974511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (19044)
      previous := (9522)
      next := (9522)
      square := (330267660922884249211084473100000000000000)
      linear := (-21521900542069538171696153896000500000000000)
      constant := (360088331521946755264248205048636375838516319) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel064
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
  base := (9488824714068221246094383874664745379649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-1042583404720677673644651927383062970250000000000)
      constant := (17714164342453688091933421305596133644851366803401) }

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
  base := (1186102653834571774156671386232024409421/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-885465135322022275605445291379120250000000000)
      constant := (15060774128111439205770816982587344111354243432) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel065
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
  base := (40159569216582107443687295745129616738787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-4235460994389278666668406494311121281000000000000)
      constant := (73138041925833970509634792426621303077557308298363) }

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
  base := (20079778629264985022652227850273607461009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-1798586597380456510514392699940440500000000000)
      constant := (31091329980859079592328579009292756306096774641) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel066
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
  base := (42414830124650895559761201885728513379073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (404075592)
      previous := (202037796)
      next := (202037796)
      square := (7007619229461757999760790350235800000000000000)
      linear := (-477843152210649626528689475454443409000000000000)
      constant := (8383958742104517065055850751463531588374011706753) }

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
  base := (42414819864451860456132690479550038996029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (342792)
      previous := (171396)
      next := (171396)
      square := (5944817896611916485799520515800000000000000)
      linear := (-405831760914859659959532181582809000000000000)
      constant := (7128111095323623279730433351479531735660094069) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel067
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
  base := (44721077668003085177441101318515835918457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-4365715745402414610848004063868860081000000000000)
      constant := (77809417431517786318226689436254080809515672000193) }

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
  base := (44721068866609985588759698540695702287591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-3707798501706560858242793868609681000000000000)
      constant := (66154116035037995737258666799856997147320986759) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel068
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
  base := (735598570941644425984799714114319753203/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-1107710780227245645734450712161932370250000000000)
      constant := (20049852004140567104259078623290636684405592242352) }

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
  base := (5884787623993171587456256686695573070411/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-940777788794846194212449525743520250000000000)
      constant := (17046502088211753480155927110701514220988081878) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel069
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
  base := (24743259973639857798344906025230992670621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (6623458628980867674632126985100000000000000)
      linear := (-472166613780251055978534092987460500000000000)
      constant := (8677336724736687287140875068130193851242618189) }

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
  base := (9897302695006067170506514339232088555083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (648)
      previous := (324)
      next := (324)
      square := (11237841014389256116823290200000000000000)
      linear := (-802021383879901007237303578521000000000000)
      constant := (14755025560353676360635526390314443984978735) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel070
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
  base := (3246606845485042556355709279359996316691/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-1140274467980529631779350104551367070250000000000)
      constant := (21271998535347986086845872060630430145142367653036) }

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
  base := (51945703979345360841956789721161333013523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-3873736462125032614063806571702881000000000000)
      constant := (72342120954910988770155417996902711958296447027) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel071
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
  base := (27227937643120265508775930971394636876677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-2313112623714343249603599601492168840500000000000)
      constant := (43793294730559961514593398617120516226946036220973) }

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
  base := (3403491908172749888864596250533037301117/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-982262278899464133167702701516820250000000000)
      constant := (18616585263614769134954316064968223211262249332) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel072
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
  base := (57017015536402830826797046876581052595533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (404075592)
      previous := (202037796)
      next := (202037796)
      square := (7007619229461757999760790350235800000000000000)
      linear := (-521261402548361607921888665307023009000000000000)
      constant := (10013487351883528712904162436303906944715599076813) }

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
  base := (11403402292270524337030348061381447918927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (38088)
      previous := (19044)
      next := (19044)
      square := (660535321845768498422168946200000000000000)
      linear := (-49189651470008400633059444943601000000000000)
      constant := (945942431111343561831384716911225929745561915) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel073
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
  base := (59629128853192996898394839490964392146091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-4756479998441822443386796772542076481000000000000)
      constant := (92692384186908728704209523277134822176418983913859) }

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
  base := (5962912536188548481931548703562387685961/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-2019837211271752184942409637398040500000000000)
      constant := (39403554245603165333848394777091830249778714445) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel074
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
  base := (62292214032347042210873749876591495684489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-4821607373948390415476595557320945881000000000000)
      constant := (95299583460164123458405305160909794314109417236561) }

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
  base := (15573052760430889845999177459202841355709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-1023746769004082072122955877290120250000000000)
      constant := (20255913929250972824202832306557931049250774941) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel075
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
  base := (16251567514047335266345571231559820488281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14030402500000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (1751904807365439499940197587558950000000000000)
      linear := (-135742631929304399654622065058328202250000000000)
      constant := (2720638442647658543442932742455192865586331585241) }

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
  base := (8125783436864402814153029260617985170871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11902500000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (1486204474152979121449880128950000000000000)
      linear := (-115286103596920894641634103986802250000000000)
      constant := (2313082737619652480763938395122898204797033662) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel076
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
  base := (6777129606472835266912967488985444196319/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-2475931062480763179828096563439342340500000000000)
      constant := (50311292784462891075362729513602604179881602591155) }

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
  base := (67771293871553943639066648757283887199339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-4205612382961976125705831977889281000000000000)
      constant := (85549076966699479771462855517848213282604476811) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel077
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
  base := (17646822832807414241997478439879692777219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-1254247375117023582936497977914388520250000000000)
      constant := (25834597081071848023119122829333487939591611442331) }

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
  base := (70587289453577744469640139759115254131819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-4260925036434800044312836212253681000000000000)
      constant := (87857950923411624980865619556358866524294312331) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel078
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
  base := (73454255241572772529167555718049163248459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (404075592)
      previous := (202037796)
      next := (202037796)
      square := (7007619229461757999760790350235800000000000000)
      linear := (-564679652886073589315087855159602609000000000000)
      constant := (11787821352264627805823716344537544437065634909899) }

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
  base := (7345425363432162546224745700177866515633/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (2972408948305958242899760257900000000000000)
      linear := (-239790982772645775717768913701004500000000000)
      constant := (5010977799913829798350279992828185112404643565) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel079
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
  base := (4773261704800353284111985046871010863617/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-1286811062870307568981397370303823220250000000000)
      constant := (27219649270249143672224767708591629846552235268132) }

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
  base := (76372185901240967979642018112576086558577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-4371550343380447881526844680982481000000000000)
      constant := (92568025369849389575793737653405871732948465873) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel080
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
  base := (79341086998401541269243822054720522729737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-5212371626987798248015388265994162281000000000000)
      constant := (111703003033982420597313049126336058932070991784913) }

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
  base := (15868217164262834561658762264855992811457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-4426862996853271800133848915346881000000000000)
      constant := (94969225819058442092631165429640552179890604965) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel081
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
  base := (4118047701789979843201820171988198664043/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14030402500000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (1751904807365439499940197587558950000000000000)
      linear := (-146597194513732395002921862521473102250000000000)
      constant := (3182322500295065667654687999421627871637971134615) }

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
  base := (2059023825717726290485898684662471880341/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (9522)
      previous := (4761)
      next := (4761)
      square := (165133830461442124605542236550000000000000)
      linear := (-13833875463969431230681645523800250000000000)
      constant := (300620992995063427417030835685559726247003890) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel082
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
  base := (10678973509484440758856234257741393508443/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-1335656594500233548048746458887975270250000000000)
      constant := (29365104498775167370655894681030994845457265555814) }

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
  base := (667435837612202489091047358907321700059/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-1134372075949729909336964346018920250000000000)
      constant := (24965988272658161218501654388106344980826498912) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel083
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
  base := (88553588854043271998992517167442303849763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-5407753753507502164284784620330770481000000000000)
      constant := (120393426974053240991845989519074703442242107910587) }

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
  base := (44276794058586384342377650926111794016617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-2296400478635871777977430809220040500000000000)
      constant := (51178739944283425573893629118328975761818021833) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel084
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
  base := (91726356146735104552305388554541979054749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (404075592)
      previous := (202037796)
      next := (202037796)
      square := (7007619229461757999760790350235800000000000000)
      linear := (-608097903223785570708287045012182209000000000000)
      constant := (13706959659576421744655366119553151373713879202589) }

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
  base := (22931588879141481456661022459767563234059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11902500000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (1486204474152979121449880128950000000000000)
      linear := (-129114266965126874293385162577902250000000000)
      constant := (2913382836520881171166368150660842368557354899) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel085
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
  base := (1899001795300931963022298423353334945367/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-2769004252260319054232191094944254640500000000000)
      constant := (63184023935981437581544838961496947546323306819575) }

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
  base := (47475044613102204562456505333630517153277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-2351713132108695696584435043584440500000000000)
      constant := (53718429880601452310919824889242926529500766173) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel086
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
  base := (1534762336708844603570580282680695852779/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-1400783970006801520138545243666844670250000000000)
      constant := (32352414943329145111763877037555799920117238540336) }

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
  base := (49112394544339550874113107127649629843777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-2379369458845107655887937160766640500000000000)
      constant := (55011356410587787640116268730301241989176000673) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel087
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
  base := (25387613841208969857550586108705599920719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14030402500000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (1751904807365439499940197587558950000000000000)
      linear := (-157451757098160390351221659984618002250000000000)
      constant := (3680207573151036909983116735926191489731662263759) }

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
  base := (50775227485510776479350096211338625814691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (2972408948305958242899760257900000000000000)
      linear := (-267447309509057735021271030883204500000000000)
      constant := (6257741182720676055083352557117424697503743851) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel088
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
  base := (104927087097517040066447255256979440713497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-5733390631040342024733778544225117481000000000000)
      constant := (135601486446570122349450739667540298982766900333153) }

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
  base := (20985417352182537212068465709419188310927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-4869364224635863148989882790262081000000000000)
      constant := (115286745159779925638296487851370441999674555115) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel089
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
  base := (108354684651147697770120245732080498950301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-5798518006546909996823577329003986881000000000000)
      constant := (138751701207852828781376461992381699772124781894149) }

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
  base := (108354684363479492409513010278308078881753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-4924676878108687067596887024626481000000000000)
      constant := (117964924429533631673249649180777131872004234297) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel090
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
  base := (55916623972201986623112660363831067245173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-325758076780748776050743117432380904500000000000)
      constant := (7885450939620990206746478516473315868681737348853) }

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
  base := (27958311924647131828635141811284104595863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (9522)
      previous := (4761)
      next := (4761)
      square := (165133830461442124605542236550000000000000)
      linear := (-15370338060436762303098429811700250000000000)
      constant := (372450244119752003471501205594441791331211527) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel091
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
  base := (57681388454292532105417273024266438040731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-2964386378780022970501587449280862840500000000000)
      constant := (72580366779537533750206026034023438456379962367219) }

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
  base := (115362776698559164074911890772760691960851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-5035302185054334904810895493355281000000000000)
      constant := (123413609152677930819356425953229093889830504499) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel092
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
  base := (118943271485656980875786896934522956214721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (6874632)
      previous := (3437316)
      next := (3437316)
      square := (119222255321655618143378285731800000000000000)
      linear := (-11330624070069213446300517359812089000000000000)
      constant := (280566259248796399377752624240173424382337775801) }

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
  base := (59471635653115755010546160381641811950931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (2916)
      previous := (1458)
      next := (1458)
      square := (50570284564751652525704805900000000000000)
      linear := (-4811545215999204937067958154744500000000000)
      constant := (119266648960982261357299493905606986768025411) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel093
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
  base := (61287365813299673854395451410536015108509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-336612639365176771399042914895525804500000000000)
      constant := (8428587203406473048599152659773256525337384977949) }

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
  base := (61287365736666991630470180888596026522079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (2972408948305958242899760257900000000000000)
      linear := (-285884860666665707890272442338004500000000000)
      constant := (7165855302047509177903851970623374182271618119) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel094
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
  base := (15782144661251040596204151557129278816451/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-1531038721019937464318142813224583470250000000000)
      constant := (38761447278273360292602127928127166599322624290998) }

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
  base := (7891072322444004889543388935260057883559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-1300310036368201665157977049112120250000000000)
      constant := (32954362914834774069319976933587286381010478364) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel095
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
  base := (12999054844091597399697342821931743461321/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (31534286532577910998923556576061100000000000000)
      linear := (-3094641129793158914681185018838601640500000000000)
      constant := (79206604748088931436778999023719297767953382610645) }

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
  base := (129990548329123054867632691205007532914881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (53503361069507248372195684642200000000000000)
      linear := (-5256552798945630579238912430812881000000000000)
      constant := (134680283266696217147849946080573562777869735969) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel096
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
  base := (13377490504979254145944341536866714737567/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (3503809614730878999880395175117900000000000000)
      linear := (-347467201949604766747342712358670704500000000000)
      constant := (8989823933837680465780789921048383425241493761435) }

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
  base := (133774904954331375292205866763442009522669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (342792)
      previous := (171396)
      next := (171396)
      square := (5944817896611916485799520515800000000000000)
      linear := (-590207272490939388649546296130809000000000000)
      constant := (15285987806409039519515078984010411407337427109) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel097
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
  base := (27522045418340664054337975230379749235891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3636680328)
      previous := (1818340164)
      next := (1818340164)
      square := (63068573065155821997847113152122200000000000000)
      linear := (-6319537010599453773541967607234942081000000000000)
      constant := (165256653050535159396141472066959291467815127170295) }

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
  base := (34402556752549214214097866001961511202941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13375840267376812093048921160550000000000000)
      linear := (-1341794526472819604113230224885420250000000000)
      constant := (35124568157810833091566599285970088043534818909) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell103.Kernel098
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
  base := (1414965145455961480659914002645327549809/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126273622500000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (15767143266288955499461778288030550000000000000)
      linear := (-1596166096526505436407941598003452870250000000000)
      constant := (42183169054871315697091903672930396102384316131025) }

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
  base := (70748257238005928646863888011599862968311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (26751680534753624186097842321100000000000000)
      linear := (-2711245379682051167529962566953040500000000000)
      constant := (71726715193247422728133193632165911528329158039) }

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
end ForestUnimodality.Stage80KernelData.Cell103.Kernel098
