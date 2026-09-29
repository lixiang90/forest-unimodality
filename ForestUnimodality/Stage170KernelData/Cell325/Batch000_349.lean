import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell325.Parameters
import ForestUnimodality.BinomialMassData.Q41_63.Batch000_049
import ForestUnimodality.BinomialMassData.Q41_63.Batch050_099
import ForestUnimodality.BinomialMassData.Q83_126.Batch000_049
import ForestUnimodality.BinomialMassData.Q83_126.Batch050_099

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree000.table
  base := (4862263587411140170475576379/500000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (41)
      previous := (0)
      next := (22)
      square := (374402584942951453111925640000000000000)
      linear := (-823960981555703058515360827500000000000)
      constant := (218801861433501307671400937055000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree000.table
  base := (4862263587411140170475576379/500000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (83)
      previous := (0)
      next := (43)
      square := (748805169885902906223851280000000000000)
      linear := (-1647921963111406117030721655000000000000)
      constant := (437603722867002615342801874110000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree001.table
  base := (77905160323697845654159477575262887377173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-2313095506493276731566077769150000000000000)
      constant := (310431208862822297131503999393228399999999637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree001.table
  base := (77671613509849242700449532891929554043839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-2323578778871679372253211687070000000000000)
      constant := (309522661059789592627688829300063399999996991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (30184421155165788947/100000000000000000000)
  directionHi := (7546105288791447237/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree002.table
  base := (12459527446131222681505399512718025951121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-3172723841522293267911059038590000000000000)
      constant := (250270017907084410812703516457989224999996245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree002.table
  base := (15480573534242714665123289473486818153187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-1596845193139549274642663437215000000000000)
      constant := (124415404132646838756963089062973362499998406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30184421155165788947/100000000000000000000)
  centralHi := (7546105288791447237/25000000000000000000)
  directionLo := (10671804442504205793/25000000000000000000)
  directionHi := (42687217770016823173/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree003.table
  base := (24846396935997145669559051656385114323507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4018)
      previous := (0)
      next := (2156)
      square := (36691453324409242404968712720000000000000)
      linear := (-224019565363961655792002239335000000000000)
      constant := (11254772415532199401622846818980835416666587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree003.table
  base := (4924037106200828933946499340775898526077/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-225766777427028762573191225655000000000000)
      constant := (11160367785249226322822731245223356249999785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671804442504205793/25000000000000000000)
  centralHi := (42687217770016823173/100000000000000000000)
  directionLo := (52280951037804008779/100000000000000000000)
  directionHi := (2614047551890200439/5000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree004.table
  base := (7900642343562040113094183070151202983839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-4891980511580326340601021577470000000000000)
      constant := (165047401435126084392566978619670623214284955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree004.table
  base := (19509236141780046598818167095274979641327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-2466956800546968451674778624575000000000000)
      constant := (81639718596902230023577275527776394196426863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/100000000000000000000)
  centralHi := (2614047551890200439/5000000000000000000)
  directionLo := (12073768462066315579/20000000000000000000)
  directionHi := (7546105288791447237/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree005.table
  base := (31268176358176079245435114311643945574803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-5751608846609342876946002846910000000000000)
      constant := (135825936280720609555245106528764819986393107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree005.table
  base := (384765897999335351749301129712002970209/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-2902012604250678040190836218255000000000000)
      constant := (67061345350671565273828470187465091550380840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12073768462066315579/20000000000000000000)
  centralHi := (7546105288791447237/12500000000000000000)
  directionLo := (67494417564433431477/100000000000000000000)
  directionHi := (33747208782216715739/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree006.table
  base := (24635872749379219476182410681681540860983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8036)
      previous := (0)
      next := (4312)
      square := (73382906648818484809937425440000000000000)
      linear := (-734581909070928823698998235150000000000000)
      constant := (12613906011985269672324460598761559519693503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree006.table
  base := (6041589076063200619377037642290566291237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-370785378661598625411877090215000000000000)
      constant := (6220997875870761388841731568565279468871034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67494417564433431477/100000000000000000000)
  centralHi := (33747208782216715739/50000000000000000000)
  directionLo := (18484107502856541973/25000000000000000000)
  directionHi := (73936430011426167893/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree007.table
  base := (19266756976616352884050098735530774718137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (1476)
      previous := (0)
      next := (792)
      square := (13478493057946252312029323040000000000000)
      linear := (-152466643197293386727264599710000000000000)
      constant := (1975457247320660504173975840327992752169097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree007.table
  base := (18826583699179175204333022944175149881671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (1494)
      previous := (0)
      next := (774)
      square := (13478493057946252312029323040000000000000)
      linear := (-153964253537065192539712302270000000000000)
      constant := (1948315181201981294874308726283187140415351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18484107502856541973/25000000000000000000)
  centralHi := (73936430011426167893/100000000000000000000)
  directionLo := (79860471845005650117/100000000000000000000)
  directionHi := (39930235922502825059/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree008.table
  base := (7457587854701927340673217115063326375819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-4165246925848196242990473327615000000000000)
      constant := (42333845622282957866855292994846342385625611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree008.table
  base := (14510933169977152767804480066449220644463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-8414360030723613611478017998590000000000000)
      constant := (83594835268515304286400949744336956737873647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79860471845005650117/100000000000000000000)
  centralHi := (39930235922502825059/50000000000000000000)
  directionLo := (10671804442504205793/12500000000000000000)
  directionHi := (17074887108006729269/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree009.table
  base := (11383180957889332487021995935348743251139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8036)
      previous := (0)
      next := (4312)
      square := (73382906648818484809937425440000000000000)
      linear := (-1021124687413934335813991991630000000000000)
      constant := (8483372990411548308676922440818795773752299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree009.table
  base := (688608538259625644489579546727295957249/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-515803979896168488250562954775000000000000)
      constant := (4197761957099819031000689148611400137174472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671804442504205793/12500000000000000000)
  centralHi := (17074887108006729269/20000000000000000000)
  directionLo := (90553263465497366843/100000000000000000000)
  directionHi := (22638315866374341711/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree010.table
  base := (8511368736591325575191814673332276961893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-10049750521754425558670909194110000000000000)
      constant := (71212727707750504216632521442155807261753317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree010.table
  base := (4092538616254772967578636382163551553461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-5077291622769225982771124186655000000000000)
      constant := (35359718002264898458783052730582136115686709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90553263465497366843/100000000000000000000)
  centralHi := (22638315866374341711/25000000000000000000)
  directionLo := (5965720044005912541/6250000000000000000)
  directionHi := (95451520704094600657/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree011.table
  base := (6171409836062055826695903420933820419697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-10909378856783442095015890463550000000000000)
      constant := (68745464994407392694385255919196333245777393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree011.table
  base := (735373694245670158422910597838210820587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-5512347426472935571287181780335000000000000)
      constant := (34279082310095152116485729911451934987639212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5965720044005912541/6250000000000000000)
  centralHi := (95451520704094600657/100000000000000000000)
  directionLo := (25027599871437707727/25000000000000000000)
  directionHi := (100110399485750830909/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree012.table
  base := (852001271848724549562532740451631621969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8036)
      previous := (0)
      next := (4312)
      square := (73382906648818484809937425440000000000000)
      linear := (-1307667465756939847928985748110000000000000)
      constant := (7615397713361310350196609005295847726441645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree012.table
  base := (4007168547959758145276649794942213581677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8134)
      previous := (0)
      next := (4214)
      square := (73382906648818484809937425440000000000000)
      linear := (-1321645162261476702178497638670000000000000)
      constant := (7629101601824098277150011795349516189519557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25027599871437707727/25000000000000000000)
  centralHi := (100110399485750830909/100000000000000000000)
  directionLo := (52280951037804008779/50000000000000000000)
  directionHi := (104561902075608017559/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree013.table
  base := (134700777758178203179686212505067880149/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (18081)
      previous := (0)
      next := (9702)
      square := (165111539959841590822359207240000000000000)
      linear := (-3157158881710368791926463250607500000000000)
      constant := (17565519351668500704878777817005572081556905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree013.table
  base := (30923867990673411031181700226744828679/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-6382459033880354748319296967695000000000000)
      constant := (35349230570143243865303672560285509001078040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/50000000000000000000)
  centralHi := (104561902075608017559/100000000000000000000)
  directionLo := (108831478195150231411/100000000000000000000)
  directionHi := (27207869548787557853/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree014.table
  base := (175815027565751234929441958037382030269/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (369)
      previous := (0)
      next := (198)
      square := (3369623264486563078007330760000000000000)
      linear := (-68817672764645365836994052407500000000000)
      constant := (375767166192819969826227852097055888903578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree014.table
  base := (121604210188486720128841172079320483297/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (747)
      previous := (0)
      next := (387)
      square := (6739246528973126156014661520000000000000)
      linear := (-139132955869062537486435807375000000000000)
      constant := (759195985325026620585298512937124795735285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108831478195150231411/100000000000000000000)
  centralHi := (27207869548787557853/25000000000000000000)
  directionLo := (56469881190360849501/50000000000000000000)
  directionHi := (112939762380721699003/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree015.table
  base := (42957969246309938043167403526769926707/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (2009)
      previous := (0)
      next := (1078)
      square := (18345726662204621202484356360000000000000)
      linear := (-398552561024986340010994876147500000000000)
      constant := (2180269001966893863569329581398111075355574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree015.table
  base := (179666365104523350261294425299922725341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8134)
      previous := (0)
      next := (4214)
      square := (73382906648818484809937425440000000000000)
      linear := (-1611682364730616427855869367790000000000000)
      constant := (8839580100379507944367912238482265921875381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56469881190360849501/50000000000000000000)
  centralHi := (112939762380721699003/100000000000000000000)
  directionLo := (2922594011221698527/2500000000000000000)
  directionHi := (116903760448867941081/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree016.table
  base := (-268949076767240689135329633435955760817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-7603760265964262388370398405375000000000000)
      constant := (42304001167587277822309979905772691585317327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree016.table
  base := (-42404298981378644739492877123516788173/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-7687626444991483513867469748735000000000000)
      constant := (42995920447953419542242764634334094941930904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2922594011221698527/2500000000000000000)
  centralHi := (116903760448867941081/100000000000000000000)
  directionLo := (12073768462066315579/10000000000000000000)
  directionHi := (120737684620663155791/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree017.table
  base := (-1273048980914686248700613861986380652971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-16067148866957541313085778080190000000000000)
      constant := (91866866839035290051049260265826055188358101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree017.table
  base := (-1393068748921162779945004911608467900987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-16245364497390386204767054684830000000000000)
      constant := (93570320789317246475538280749420990900982597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12073768462066315579/10000000000000000000)
  centralHi := (120737684620663155791/100000000000000000000)
  directionLo := (3889173645964899637/3125000000000000000)
  directionHi := (24890711334175357677/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree018.table
  base := (-472465673238718776589369496558669515491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (2009)
      previous := (0)
      next := (1078)
      square := (18345726662204621202484356360000000000000)
      linear := (-470188255610737718039743315267500000000000)
      constant := (2782079222671104145836493170362626743668469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree018.table
  base := (-1991981548000045616323100244931236090409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8134)
      previous := (0)
      next := (4214)
      square := (73382906648818484809937425440000000000000)
      linear := (-1901719567199756153533241096910000000000000)
      constant := (11353459089155404033143434290935324884129631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3889173645964899637/3125000000000000000)
  centralHi := (24890711334175357677/20000000000000000000)
  directionLo := (32015413327512617379/25000000000000000000)
  directionHi := (128061653310050469517/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree019.table
  base := (-2410932874005606918510855967307269041029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-17786405537015574385775740619070000000000000)
      constant := (109382283930260564700720381836627449176155899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree019.table
  base := (-1248776311466409252360105714498931377067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-8992793856102612279415642529775000000000000)
      constant := (55867792437938189647899815258346241364421077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32015413327512617379/25000000000000000000)
  centralHi := (128061653310050469517/100000000000000000000)
  directionLo := (65785420742319457321/50000000000000000000)
  directionHi := (131570841484638914643/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree020.table
  base := (-713610623376585704430894739169668867627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (18081)
      previous := (0)
      next := (9702)
      square := (165111539959841590822359207240000000000000)
      linear := (-4661508468011147730530180472127500000000000)
      constant := (29869248593908128791931816634085584264388437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree020.table
  base := (-2927712042928617718983262088142355622873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-18855699319612643735863400246910000000000000)
      constant := (122162515565059413597166006579262990532817063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65785420742319457321/50000000000000000000)
  centralHi := (131570841484638914643/100000000000000000000)
  directionLo := (67494417564433431477/50000000000000000000)
  directionHi := (26997767025773372591/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree021.table
  base := (-1617512445687225795420329966702182836373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (82)
      previous := (0)
      next := (44)
      square := (748805169885902906223851280000000000000)
      linear := (-22115263273326085553815989975000000000000)
      constant := (147824153771137827592002893104680354472643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree021.table
  base := (-659369386596785977542686776420810272543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (166)
      previous := (0)
      next := (86)
      square := (1497610339771805812447702560000000000000)
      linear := (-44729729993242773045114547470000000000000)
      constant := (302505263879448262524879697956063537735565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67494417564433431477/50000000000000000000)
  centralHi := (26997767025773372591/20000000000000000000)
  directionLo := (138322394751973624287/100000000000000000000)
  directionHi := (4322574835999175759/3125000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree022.table
  base := (-891114178810365975745638624512407517639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (18081)
      previous := (0)
      next := (9702)
      square := (165111539959841590822359207240000000000000)
      linear := (-5091322635525655998702671106847500000000000)
      constant := (35511817541836041449028787275985254562490809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree022.table
  base := (-1808250771168899333182167123412170312123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-10297961267213741044963815310815000000000000)
      constant := (72708341583989212778111041630762096031183813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138322394751973624287/100000000000000000000)
  centralHi := (4322574835999175759/3125000000000000000)
  directionLo := (35394371171834336301/25000000000000000000)
  directionHi := (28315496937467469041/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree023.table
  base := (-3852215600810929515197867530027969785107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-21224918877131640531155665696830000000000000)
      constant := (154438477263126931746031145926788987922910317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree023.table
  base := (-1947969498280299424648662703157533769451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-10733017070917450633479872904495000000000000)
      constant := (79080667805547910693298084650430248469048981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35394371171834336301/25000000000000000000)
  centralHi := (28315496937467469041/20000000000000000000)
  directionLo := (144759398488891423273/100000000000000000000)
  directionHi := (72379699244445711637/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree024.table
  base := (-4105928991381632178995642913552092979993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8036)
      previous := (0)
      next := (4312)
      square := (73382906648818484809937425440000000000000)
      linear := (-2453838579128961896388960774030000000000000)
      constant := (18613805732337665452906127445603526995823087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree024.table
  base := (-1035648014029926396023614957219457531949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-1240896986069017802443992277575000000000000)
      constant := (9533848781882992183546724370552438456820982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144759398488891423273/100000000000000000000)
  centralHi := (72379699244445711637/50000000000000000000)
  directionLo := (18484107502856541973/12500000000000000000)
  directionHi := (29574572004570467157/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree025.table
  base := (-433173534321033089129485558370779874021/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-11472087773594836801922814117855000000000000)
      constant := (90640114809098630663857870418756873400053255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree025.table
  base := (-1090606202209870102607701632092607741541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-11603128678324869810511988091855000000000000)
      constant := (92868419545898824178493171226386379747647542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18484107502856541973/12500000000000000000)
  centralHi := (29574572004570467157/20000000000000000000)
  directionLo := (75461052887914472369/50000000000000000000)
  directionHi := (150922105775828944739/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree026.table
  base := (-566821852223227271843885659233664746383/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (18081)
      previous := (0)
      next := (9702)
      square := (165111539959841590822359207240000000000000)
      linear := (-5950950970554672535047652376287500000000000)
      constant := (48921700960913182744573232861568169243211746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree026.table
  base := (-2280111446460394629875135191511651107131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-12038184482028579399028045685535000000000000)
      constant := (100262512233393975832065611093825256755797061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75461052887914472369/50000000000000000000)
  centralHi := (150922105775828944739/100000000000000000000)
  directionLo := (76955476238346612779/50000000000000000000)
  directionHi := (153910952476693225559/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree027.table
  base := (-1179605806229167864957518023737968949461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (2009)
      previous := (0)
      next := (1078)
      square := (18345726662204621202484356360000000000000)
      linear := (-685095339367991852125988632627500000000000)
      constant := (5853560952174309839065783231569055693287699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree027.table
  base := (-947965274267699821977997809174516595643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8134)
      previous := (0)
      next := (4214)
      square := (73382906648818484809937425440000000000000)
      linear := (-2771831174607175330565356284270000000000000)
      constant := (23995399220990835798915564281075190906607185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76955476238346612779/50000000000000000000)
  centralHi := (153910952476693225559/100000000000000000000)
  directionLo := (156842853113412026337/100000000000000000000)
  directionHi := (78421426556706013169/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree028.table
  base := (-4886480294329174469406714433838156613233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (1476)
      previous := (0)
      next := (792)
      square := (13478493057946252312029323040000000000000)
      linear := (-520878786781157616589399429470000000000000)
      constant := (4620238799893487977874511506339109314328127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree028.table
  base := (-4904316588911170628046562940316199450133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (1494)
      previous := (0)
      next := (774)
      square := (13478493057946252312029323040000000000000)
      linear := (-526869228140244839839190239710000000000000)
      constant := (4735210506134724339738971518334387844539227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156842853113412026337/100000000000000000000)
  centralHi := (78421426556706013169/50000000000000000000)
  directionLo := (79860471845005650117/50000000000000000000)
  directionHi := (31944188738002260047/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree029.table
  base := (-2520660595676803277247717671125259791133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-13191344443652869874612776656735000000000000)
      constant := (121333551880987061181282644388188843888993123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree029.table
  base := (-1264041526179772402040344310867265768829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-13343351893139708164576218466575000000000000)
      constant := (124357688157425104359443221012903144327035398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79860471845005650117/50000000000000000000)
  centralHi := (31944188738002260047/20000000000000000000)
  directionLo := (162548082528525019217/100000000000000000000)
  directionHi := (81274041264262509609/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree030.table
  base := (-1296254613013974755521583440304892246307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (2009)
      previous := (0)
      next := (1078)
      square := (18345726662204621202484356360000000000000)
      linear := (-756731033953743230154737071747500000000000)
      constant := (7209616002339141866362976903800542519378613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree030.table
  base := (-5197358996094774256033408279454087879217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8134)
      previous := (0)
      next := (4214)
      square := (73382906648818484809937425440000000000000)
      linear := (-3061868377076315056242728013390000000000000)
      constant := (29557878080970100627383828264610747245265303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162548082528525019217/100000000000000000000)
  centralHi := (81274041264262509609/50000000000000000000)
  directionLo := (5166465109975139501/3125000000000000000)
  directionHi := (165326883519204464033/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree031.table
  base := (-2659620056279224351161330688538146309539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-14050972778681886410957757926175000000000000)
      constant := (138511148863058036188259068574447097297439709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree031.table
  base := (-5329487388823825210900455298387441662879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-28426927001094254683216667307870000000000000)
      constant := (283935574895000534492778816241745244040033249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5166465109975139501/3125000000000000000)
  centralHi := (165326883519204464033/100000000000000000000)
  directionLo := (168059744420384683169/100000000000000000000)
  directionHi := (16805974442038468317/10000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree032.table
  base := (-5445328680035591875589407493234742646853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-28961573892392789358260497121790000000000000)
      constant := (295090140276720077228070172067351306434640443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree032.table
  base := (-5453828911395807962799323063629808660339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-29297038608501673860248782495230000000000000)
      constant := (302454321906184009827903449500773289427114509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168059744420384683169/100000000000000000000)
  centralHi := (16805974442038468317/10000000000000000000)
  directionLo := (10671804442504205793/6250000000000000000)
  directionHi := (170748871080067292689/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree033.table
  base := (-2782182342814802814618247183689062831259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4018)
      previous := (0)
      next := (2156)
      square := (36691453324409242404968712720000000000000)
      linear := (-1656733457078989216366971021735000000000000)
      constant := (17430300839328745776890635102858123291414781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree033.table
  base := (-2785704421443876749249621531212116889763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-1675952789772727390960049871255000000000000)
      constant := (17865170801645810870296737465872956451614517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671804442504205793/6250000000000000000)
  centralHi := (170748871080067292689/100000000000000000000)
  directionLo := (43349074568834411197/25000000000000000000)
  directionHi := (173396298275337644789/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree034.table
  base := (-1135443565875534291073999456081909406091/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-30680830562450822430950459660670000000000000)
      constant := (332984670380260539302232903711274507836124105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree034.table
  base := (-5683049979204021496788685557530585929771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-31037261823316512214313012869950000000000000)
      constant := (341288566788377888439980852423671104444738901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43349074568834411197/25000000000000000000)
  centralHi := (173396298275337644789/100000000000000000000)
  directionLo := (44000976932380632591/25000000000000000000)
  directionHi := (35200781545904506073/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree035.table
  base := (-5784588139609710900255855538382415162797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (1476)
      previous := (0)
      next := (792)
      square := (13478493057946252312029323040000000000000)
      linear := (-643682834642445693210111039390000000000000)
      constant := (7200104646557305399296838255941024371813443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree035.table
  base := (-5789412644706783720811158677304708455203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (1494)
      previous := (0)
      next := (774)
      square := (13478493057946252312029323040000000000000)
      linear := (-651170886341304722272349552190000000000000)
      constant := (7379554656225518947426644894963318615128557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44000976932380632591/25000000000000000000)
  centralHi := (35200781545904506073/20000000000000000000)
  directionLo := (178573443760640682589/100000000000000000000)
  directionHi := (17857344376064068259/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree036.table
  base := (-73587988704433241251689239720258277641/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (2009)
      previous := (0)
      next := (1078)
      square := (18345726662204621202484356360000000000000)
      linear := (-900002423125245986212233949987500000000000)
      constant := (10366793071078468206234087149077321991206380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree036.table
  base := (-5891026796677221186810827006366246630393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8134)
      previous := (0)
      next := (4214)
      square := (73382906648818484809937425440000000000000)
      linear := (-3641942782014594507597471471630000000000000)
      constant := (42499978347688134240404714159772485235996687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178573443760640682589/100000000000000000000)
  centralHi := (17857344376064068259/10000000000000000000)
  directionLo := (90553263465497366843/50000000000000000000)
  directionHi := (181106526930994733687/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree037.table
  base := (-5985024287689635251728920403022890446703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-33259715567537872039985403468990000000000000)
      constant := (394181138721733128168493156607052147817035793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree037.table
  base := (-5988317785217181273125661560093697947007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-33647596645538769745409358432030000000000000)
      constant := (403991759496251995414567928217883112848329217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90553263465497366843/50000000000000000000)
  centralHi := (181106526930994733687/100000000000000000000)
  directionLo := (91802333000691682819/50000000000000000000)
  directionHi := (183604666001383365639/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree038.table
  base := (-189965901926960962734475491330165639061/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (18081)
      previous := (0)
      next := (9702)
      square := (165111539959841590822359207240000000000000)
      linear := (-8529835975641722144082596184607500000000000)
      constant := (103933360724357456515376378185439580628535128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree038.table
  base := (-380101688900732286439151953539185936389/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-17258854126473094461220736809695000000000000)
      constant := (213036343095830608197150210178448768147776472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91802333000691682819/50000000000000000000)
  centralHi := (183604666001383365639/100000000000000000000)
  directionLo := (46517317110104249321/25000000000000000000)
  directionHi := (37213853688083399457/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree039.table
  base := (-3084493394956457617639504814357965872669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4018)
      previous := (0)
      next := (2156)
      square := (36691453324409242404968712720000000000000)
      linear := (-1943276235421994728481964778215000000000000)
      constant := (24325572017360006567749039906683137050152971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree039.table
  base := (-6171228566800438706070474513461834980993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8134)
      previous := (0)
      next := (4214)
      square := (73382906648818484809937425440000000000000)
      linear := (-3931979984483734233274843200750000000000000)
      constant := (49860166386341905855987425297328330773382087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46517317110104249321/25000000000000000000)
  centralHi := (37213853688083399457/20000000000000000000)
  directionLo := (188501649696824618569/100000000000000000000)
  directionHi := (18850164969682461857/10000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree040.table
  base := (-1251098952145288388254361000389077266217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-35838600572624921649020347277310000000000000)
      constant := (460560759551075626733155442410078761651923635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree040.table
  base := (-625734243039390910874704823438662481201/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-18128965733880513638252851997055000000000000)
      constant := (235998660062414942941415644761959743060566155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188501649696824618569/100000000000000000000)
  centralHi := (18850164969682461857/10000000000000000000)
  directionLo := (5965720044005912541/3125000000000000000)
  directionHi := (190903041408189201313/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree041.table
  base := (-633862335961636256973657483962416843981/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-18349114453826969092682664273375000000000000)
      constant := (241917038089657564503237848592270837731197055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree041.table
  base := (-1268029051189232483919263785651845315379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-37128043075168446453537819181470000000000000)
      constant := (495839453039828652490457885027134129716303745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5965720044005912541/3125000000000000000)
  centralHi := (190903041408189201313/100000000000000000000)
  directionLo := (193274598691522888013/100000000000000000000)
  directionHi := (96637299345761444007/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree042.table
  base := (-6418526067025532379756521042019674017639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (164)
      previous := (0)
      next := (88)
      square := (1497610339771805812447702560000000000000)
      linear := (-85165209167081529981202516590000000000000)
      constant := (1151200991005262885524132095921822933841249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree042.table
  base := (-6419778884193081939035446175203275329743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (166)
      previous := (0)
      next := (86)
      square := (1497610339771805812447702560000000000000)
      linear := (-86163616060262733856167651630000000000000)
      constant := (1179744519855312316796850131093170522032313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193274598691522888013/100000000000000000000)
  centralHi := (96637299345761444007/50000000000000000000)
  directionLo := (97808703319083063177/50000000000000000000)
  directionHi := (39123481327633225271/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree043.table
  base := (-259813059974164888722691857126009004573/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-38417485577711971258055291085630000000000000)
      constant := (532096951479600759171461307722341756521244075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree043.table
  base := (-3248178614029833553357489668433066184767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-19434133144991642403801024778095000000000000)
      constant := (272640254326761400378858663731201660312659777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97808703319083063177/50000000000000000000)
  centralHi := (39123481327633225271/20000000000000000000)
  directionLo := (197932486116640440931/100000000000000000000)
  directionHi := (49483121529160110233/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree044.table
  base := (-6569124236298941189156415751491206710231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-39277113912740987794400272355070000000000000)
      constant := (557085624286337973636721911390451400567093161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree044.table
  base := (-6569971788428958625847985243557807706803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-39738377897390703984634164743550000000000000)
      constant := (570878616064814071090324481728579061211698893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197932486116640440931/100000000000000000000)
  centralHi := (49483121529160110233/25000000000000000000)
  directionLo := (25027599871437707727/12500000000000000000)
  directionHi := (200220798971501661817/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree045.table
  base := (-3319999755262578972924498437824795775457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4018)
      previous := (0)
      next := (2156)
      square := (36691453324409242404968712720000000000000)
      linear := (-2229819013765000240596958534695000000000000)
      constant := (32369185389449140084936731805844265063023463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree045.table
  base := (-1660174019985209763128571471747839002689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-2256027194711006842314793329495000000000000)
      constant := (33170075761692269380008419840305905999628302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25027599871437707727/12500000000000000000)
  centralHi := (200220798971501661817/100000000000000000000)
  directionLo := (202483252693300294431/100000000000000000000)
  directionHi := (6327601646665634201/3125000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree046.table
  base := (-6708016981798667977521556883847873067989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-40996370582799020867090234893950000000000000)
      constant := (608775833016229563650543694763267791793151659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree046.table
  base := (-6708589182231909630559082508292612134031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-41478601112205542338698395118270000000000000)
      constant := (623828517103385463670376949927156622440030961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202483252693300294431/100000000000000000000)
  centralHi := (6327601646665634201/3125000000000000000)
  directionLo := (102360352311980785991/50000000000000000000)
  directionHi := (204720704623961571983/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree047.table
  base := (-6773228774337040337789627377535348869063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-41855998917828037403435216163390000000000000)
      constant := (635476905423753568427969433238512200338688953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree047.table
  base := (-846712323681983667861686772818469418341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-21174356359806480757865255152815000000000000)
      constant := (325589943869645942158913214262256479514418284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102360352311980785991/50000000000000000000)
  centralHi := (204720704623961571983/100000000000000000000)
  directionLo := (20693396575285493953/10000000000000000000)
  directionHi := (206933965752854939531/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree048.table
  base := (-273427076849377132674856824613888958033/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8036)
      previous := (0)
      next := (4312)
      square := (73382906648818484809937425440000000000000)
      linear := (-4746180805873005993308910825870000000000000)
      constant := (73638709711478426828029144830711874237686175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree048.table
  base := (-53406738255978615465214553305266134021/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-2401045795945576705153479194055000000000000)
      constant := (37728629112312203405815064081312168633391296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20693396575285493953/10000000000000000000)
  centralHi := (206933965752854939531/100000000000000000000)
  directionLo := (52280951037804008779/25000000000000000000)
  directionHi := (209123804151216035117/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree049.table
  base := (-861924416465979712936902631940865695847/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (369)
      previous := (0)
      next := (198)
      square := (3369623264486563078007330760000000000000)
      linear := (-222322732591255461612883564807500000000000)
      constant := (3523419103924105646673264002358079757272786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree049.table
  base := (-6895711635027532904817765917198219835769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (1494)
      previous := (0)
      next := (774)
      square := (13478493057946252312029323040000000000000)
      linear := (-899774202743424487138668177150000000000000)
      constant := (14441524571011345173584024793821944193302711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/25000000000000000000)
  centralHi := (209123804151216035117/100000000000000000000)
  directionLo := (211290948086160522633/100000000000000000000)
  directionHi := (105645474043080261317/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree050.table
  base := (-695241137446825509396874174820692233357/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-22217441961457543506235079985855000000000000)
      constant := (359501033847517199257158221549933362629030335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree050.table
  base := (-1738167685764241153409084819946399448319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-22479523770917609523413427933855000000000000)
      constant := (368368964712373372086339879788140481179243778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211290948086160522633/100000000000000000000)
  centralHi := (105645474043080261317/50000000000000000000)
  directionLo := (213436088850084115861/100000000000000000000)
  directionHi := (106718044425042057931/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree051.table
  base := (-3503373575884816094435907101149891549773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4018)
      previous := (0)
      next := (2156)
      square := (36691453324409242404968712720000000000000)
      linear := (-2516361792108005752711952291175000000000000)
      constant := (41554670536497269025096169340587897826550107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree051.table
  base := (-350347987449945347318850944012104814791/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-2546064397180146567992165058615000000000000)
      constant := (42579162292354625720256390696559117766771690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213436088850084115861/100000000000000000000)
  centralHi := (106718044425042057931/50000000000000000000)
  directionLo := (215559883336611177207/100000000000000000000)
  directionHi := (26944985417076397151/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree052.table
  base := (-7058420525169922051966770102878780418973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-46154140592973120085160122510590000000000000)
      constant := (777536079362429902850130865096274120517096163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree052.table
  base := (-7058594718344717104151963763676088719599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-46699270756650057400891086242430000000000000)
      constant := (796695615728530273150208874532589603871911569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215559883336611177207/100000000000000000000)
  centralHi := (26944985417076397151/12500000000000000000)
  directionLo := (217662956390300462823/100000000000000000000)
  directionHi := (27207869548787557853/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree053.table
  base := (-5685956752686256228021312943053581581/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-23506884464001068310752551890015000000000000)
      constant := (403829019737274323433039365532522709190631875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree053.table
  base := (-71075886146960097791656126005309212863/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-23784691182028738288961600714895000000000000)
      constant := (413774980685326483008050934238433886707337650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217662956390300462823/100000000000000000000)
  centralHi := (27207869548787557853/12500000000000000000)
  directionLo := (219745902953930545189/100000000000000000000)
  directionHi := (21974590295393054519/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree054.table
  base := (-7153835094038514683411831017196034969721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8036)
      previous := (0)
      next := (4312)
      square := (73382906648818484809937425440000000000000)
      linear := (-5319266362559017017538898338830000000000000)
      constant := (93149989286115298237754356022196548578353039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree054.table
  base := (-7153951910282043687800673017928036174981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8134)
      previous := (0)
      next := (4214)
      square := (73382906648818484809937425440000000000000)
      linear := (-5382165996829432861661701846350000000000000)
      constant := (95443101847163712635219005310983736046833379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219745902953930545189/100000000000000000000)
  centralHi := (21974590295393054519/10000000000000000000)
  directionLo := (55452322508569625919/25000000000000000000)
  directionHi := (221809290034278503677/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree055.table
  base := (-7197597463682483150047932376402944175643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-48733025598060169694195066318910000000000000)
      constant := (869611634041863187874550606842406714566872933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree055.table
  base := (-899711634490091899017359906209788232493/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-24654802789436157465993715902255000000000000)
      constant := (445504723934657653105857004662275902020941132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55452322508569625919/25000000000000000000)
  centralHi := (221809290034278503677/100000000000000000000)
  directionLo := (2798170731309985587/1250000000000000000)
  directionHi := (223853658504798846961/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree056.table
  base := (-361937037148088872808743471527201321119/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (369)
      previous := (0)
      next := (198)
      square := (3369623264486563078007330760000000000000)
      linear := (-253023744556577480768061467287500000000000)
      constant := (4599200001738904513215875918091483464946805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree056.table
  base := (-7238818974245842304014257194932834292069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (1494)
      previous := (0)
      next := (774)
      square := (13478493057946252312029323040000000000000)
      linear := (-1024075860944484369571827489630000000000000)
      constant := (18849276078926229754109418454290440422342411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2798170731309985587/1250000000000000000)
  centralHi := (223853658504798846961/100000000000000000000)
  directionLo := (45175904952288679601/20000000000000000000)
  directionHi := (112939762380721699003/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree057.table
  base := (-7277271185737431163722467332639307357173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8036)
      previous := (0)
      next := (4312)
      square := (73382906648818484809937425440000000000000)
      linear := (-5605809140902022529653892095310000000000000)
      constant := (103760508627816614675530327497556065455486707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree057.table
  base := (-1819333793828663413459039504158868340207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-2836101599649286293669536787735000000000000)
      constant := (53155729695062549464545489880009378123937426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45175904952288679601/20000000000000000000)
  centralHi := (112939762380721699003/50000000000000000000)
  directionLo := (11394369112299278721/5000000000000000000)
  directionHi := (227887382245985574421/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree058.table
  base := (-7313193885485563549578479972061785755687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-51311910603147219303230010127230000000000000)
      constant := (966815745754429212932966914251706772335678297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree058.table
  base := (-3656623104966420905711116420901758843919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-25959970200547286231541888683295000000000000)
      constant := (495287624908884744506739846370615919148485489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11394369112299278721/5000000000000000000)
  centralHi := (227887382245985574421/100000000000000000000)
  directionLo := (229877702849581218817/100000000000000000000)
  directionHi := (114938851424790609409/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree059.table
  base := (-7346512999850048950295591172004394832629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-52171538938176235839574991396670000000000000)
      constant := (1000356688151375789908115978172784556909295499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree059.table
  base := (-57394966976578838803232894445422732711/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-26395026004250995820057946276975000000000000)
      constant := (512465429561125633884235047441243999127682624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229877702849581218817/100000000000000000000)
  centralHi := (114938851424790609409/50000000000000000000)
  directionLo := (231850938207876961851/100000000000000000000)
  directionHi := (57962734551969240463/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree060.table
  base := (-1844307982858673132672495074334671689039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (2009)
      previous := (0)
      next := (1078)
      square := (18345726662204621202484356360000000000000)
      linear := (-1473087979811257010442221462947500000000000)
      constant := (28735205314895965564057353426168409785133801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree060.table
  base := (-737726688676412760659327203198410893361/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-2981120200883856156508222652295000000000000)
      constant := (58881663912738545498019141876797503980138995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231850938207876961851/100000000000000000000)
  centralHi := (57962734551969240463/25000000000000000000)
  directionLo := (2922594011221698527/1250000000000000000)
  directionHi := (233807520897735882161/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree061.table
  base := (-7405353473375707024711312917735263919689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-53890795608234268912264953935550000000000000)
      constant := (1069147844223108495785766927113518737502754359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree061.table
  base := (-3702691015931726246263419829753880813911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-27265137611658414997090061464335000000000000)
      constant := (547696256946609557157426466786754347049587241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2922594011221698527/1250000000000000000)
  centralHi := (233807520897735882161/100000000000000000000)
  directionLo := (117873932772281782887/50000000000000000000)
  directionHi := (9429914621782542631/4000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree062.table
  base := (-3715439963283873829478054523235371472739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-27375211971631642724304967602495000000000000)
      constant := (552199018839843054876430500777228810624698909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree062.table
  base := (-7430903252585441583955323802513722773769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-55400386830724249171212238116030000000000000)
      constant := (1131498541400258498224971557655593034310910839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117873932772281782887/50000000000000000000)
  centralHi := (9429914621782542631/4000000000000000000)
  directionLo := (118836184924132053371/50000000000000000000)
  directionHi := (237672369848264106743/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree063.table
  base := (-1863453298518707508119156940029746496917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (41)
      previous := (0)
      next := (22)
      square := (374402584942951453111925640000000000000)
      linear := (-31524972946877722213693263307500000000000)
      constant := (646382065846216850507204382307232281527747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree063.table
  base := (-7453832241370244388940811401217889941059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (166)
      previous := (0)
      next := (86)
      square := (1497610339771805812447702560000000000000)
      linear := (-127597502127282694667220755790000000000000)
      constant := (2648952440437907068701138328714038990530469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118836184924132053371/50000000000000000000)
  centralHi := (237672369848264106743/100000000000000000000)
  directionLo := (239581415535016950351/100000000000000000000)
  directionHi := (14973838470938559397/6250000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree064.table
  base := (-7474154857177549989616305142297924109271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-56469680613321318521299897743870000000000000)
      constant := (1176607617366127054505110415804139539210303401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree064.table
  base := (-467135650418437621883840608471889676637/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-28570305022769543762638234245375000000000000)
      constant := (602730481400774449366617041470680558987421976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239581415535016950351/100000000000000000000)
  centralHi := (14973838470938559397/6250000000000000000)
  directionLo := (241475369241326311581/100000000000000000000)
  directionHi := (120737684620663155791/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree065.table
  base := (-7491906236638981388702102727423506789401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-57329308948350335057644879013310000000000000)
      constant := (1213566992077779060240366947466906101552867431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree065.table
  base := (-7491918927608177324764853239691184422803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-58010721652946506702308583678110000000000000)
      constant := (1243317346425910792659010775901740689025894893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241475369241326311581/100000000000000000000)
  centralHi := (120737684620663155791/50000000000000000000)
  directionLo := (24335458333614204061/10000000000000000000)
  directionHi := (243354583336142040611/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree066.table
  base := (-1876767110518068321222410445773169879481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (2009)
      previous := (0)
      next := (1078)
      square := (18345726662204621202484356360000000000000)
      linear := (-1616359368982759766499718341187500000000000)
      constant := (34752668996767443136126818460199032083148879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree066.table
  base := (-7507078797550913675242321205932185779533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8134)
      previous := (0)
      next := (4214)
      square := (73382906648818484809937425440000000000000)
      linear := (-6542314806705991764371188762830000000000000)
      constant := (142417463684803866873649139439213906071225947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24335458333614204061/10000000000000000000)
  centralHi := (243354583336142040611/100000000000000000000)
  directionLo := (61304849171568251939/25000000000000000000)
  directionHi := (245219396686273007757/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree067.table
  base := (-3759821205865084090089758286929525982559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-29524282809204184065167420776095000000000000)
      constant := (644597444529874298747632804234451711375223329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree067.table
  base := (-7519650859579699463466483447581489247749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-59750944867761345056372814052830000000000000)
      constant := (1320780439667429723639476672365894069175684219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61304849171568251939/25000000000000000000)
  centralHi := (245219396686273007757/100000000000000000000)
  directionLo := (247070135369801708857/100000000000000000000)
  directionHi := (123535067684900854429/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree068.table
  base := (-7529628944583753270382403341629359616137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-59908193953437384666679822821630000000000000)
      constant := (1327863404435024748944294805167993071683552247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree068.table
  base := (-7529635834686883125871875033025925202253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-60621056475168764233404929240190000000000000)
      constant := (1360387143076876927044705358454220102872257843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247070135369801708857/100000000000000000000)
  centralHi := (123535067684900854429/50000000000000000000)
  directionLo := (248907113341753576769/100000000000000000000)
  directionHi := (24890711334175357677/10000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree069.table
  base := (-7537028726193279235211055608295398603363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8036)
      previous := (0)
      next := (4312)
      square := (73382906648818484809937425440000000000000)
      linear := (-6751980254274044578113867121230000000000000)
      constant := (151900180809829752477763681770671729215916917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree069.table
  base := (-3768517172290201419411593495170087064007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-3416176004587565745024280245975000000000000)
      constant := (77809848940223200303140936362637491604772913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248907113341753576769/100000000000000000000)
  centralHi := (24890711334175357677/10000000000000000000)
  directionLo := (250730633055869305041/100000000000000000000)
  directionHi := (125365316527934652521/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree070.table
  base := (-471365146848785513890420784334288058073/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (369)
      previous := (0)
      next := (198)
      square := (3369623264486563078007330760000000000000)
      linear := (-314425768487221519078417272247500000000000)
      constant := (7178109975848847221725768281150690669184348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree070.table
  base := (-235682716562973828427752817820750297033/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (747)
      previous := (0)
      next := (387)
      square := (6739246528973126156014661520000000000000)
      linear := (-636339588673302067219073057295000000000000)
      constant := (14707661745536689237414580356929307615045232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250730633055869305041/100000000000000000000)
  centralHi := (125365316527934652521/50000000000000000000)
  directionLo := (252540986045967202841/100000000000000000000)
  directionHi := (126270493022983601421/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree071.table
  base := (-7544070332076488239769203368279842770689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-62487078958524434275714766629950000000000000)
      constant := (1447287186315457383294564742707807304043135359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree071.table
  base := (-7544074065552700140543474617295284167249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-63231391297391021764501274802270000000000000)
      constant := (1482707851609076002144738243222400017140188719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252540986045967202841/100000000000000000000)
  centralHi := (126270493022983601421/50000000000000000000)
  directionLo := (508676906940119787/200000000000000000)
  directionHi := (254338453470059893501/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree072.table
  base := (-7543713128927012606455358522743365080079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8036)
      previous := (0)
      next := (4312)
      square := (73382906648818484809937425440000000000000)
      linear := (-7038523032617050090228860877710000000000000)
      constant := (165359390958760720856331892946270175999685161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree072.table
  base := (-3771858085726327099611496205611727942329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-3561194605822135607862966110535000000000000)
      constant := (84702682271969359500668510786265227977432911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508676906940119787/200000000000000000)
  centralHi := (254338453470059893501/100000000000000000000)
  directionLo := (256123306620100939033/100000000000000000000)
  directionHi := (128061653310050469517/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree073.table
  base := (-1885192786072127855170718273916882783713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (18081)
      previous := (0)
      next := (9702)
      square := (165111539959841590822359207240000000000000)
      linear := (-16051583907145616837101182292207500000000000)
      constant := (382437887650611183943764118031816392231443103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree073.table
  base := (-301630944930424356777435120310545434823/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-64971614512205860118565505176990000000000000)
      constant := (1567172137431172528044921776215461129229687825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256123306620100939033/100000000000000000000)
  centralHi := (128061653310050469517/50000000000000000000)
  directionLo := (51579161479995644273/20000000000000000000)
  directionHi := (128947903699989110683/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree074.table
  base := (-7535244740119895446121972042265824861167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-65065963963611483884749710438270000000000000)
      constant := (1571838280799637210677765926693066941126028177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree074.table
  base := (-3767623379772713906821436097317811720241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-32920863059806639647798810182175000000000000)
      constant := (805139709936234176981223654612000605282363471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51579161479995644273/20000000000000000000)
  centralHi := (128947903699989110683/50000000000000000000)
  directionLo := (259656208774138658269/100000000000000000000)
  directionHi := (25965620877413865827/10000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree075.table
  base := (-3763567121690111849650690023598641551481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4018)
      previous := (0)
      next := (2156)
      square := (36691453324409242404968712720000000000000)
      linear := (-3662532905480027801171927317095000000000000)
      constant := (89694150440151300398806271774467999075796879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree075.table
  base := (-3763567944074870037006742789130441413183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-3706213207056705470701651975095000000000000)
      constant := (91887229277639364083382722532305975336786297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259656208774138658269/100000000000000000000)
  centralHi := (25965620877413865827/10000000000000000000)
  directionLo := (52280951037804008779/20000000000000000000)
  directionHi := (32675594398627505487/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree076.table
  base := (-234888748495647021136562416549348199087/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (18081)
      previous := (0)
      next := (9702)
      square := (165111539959841590822359207240000000000000)
      linear := (-16696305158417379239359918244287500000000000)
      constant := (414430207697442504689020595724915095982589576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree076.table
  base := (-46977758070284208733266503480670952339/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-33790974667214058824830925369535000000000000)
      constant := (849122128843176372815873599144627359213320720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/20000000000000000000)
  centralHi := (32675594398627505487/12500000000000000000)
  directionLo := (65785420742319457321/25000000000000000000)
  directionHi := (52628336593855565857/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree077.table
  base := (-300126485556635745558466701183015350783/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (1476)
      previous := (0)
      next := (792)
      square := (13478493057946252312029323040000000000000)
      linear := (-1380507121810174152934380698910000000000000)
      constant := (34724829557465975828103054574754393914664425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree077.table
  base := (-300126529177149441751690570191227855519/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (1494)
      previous := (0)
      next := (774)
      square := (13478493057946252312029323040000000000000)
      linear := (-1396980835547664016871305427070000000000000)
      constant := (35573506344993775034085735889617763592574025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65785420742319457321/25000000000000000000)
  centralHi := (52628336593855565857/20000000000000000000)
  directionLo := (4138550323291018383/1562500000000000000)
  directionHi := (264867220690625176513/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree078.table
  base := (-7487301057307277702643690701845482217051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8036)
      previous := (0)
      next := (4312)
      square := (73382906648818484809937425440000000000000)
      linear := (-7611608589303061114458848390670000000000000)
      constant := (193986906610855717253303127979266142342280509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree078.table
  base := (-7487301945042137996524883401072574272961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8134)
      previous := (0)
      next := (4214)
      square := (73382906648818484809937425440000000000000)
      linear := (-7702463616582550667080675679310000000000000)
      constant := (198726976187853047510368517544376994745624199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4138550323291018383/1562500000000000000)
  centralHi := (264867220690625176513/100000000000000000000)
  directionLo := (66645397382737899027/25000000000000000000)
  directionHi := (266581589530951596109/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree079.table
  base := (-93360711779136283532792599721949579157/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (18081)
      previous := (0)
      next := (9702)
      square := (165111539959841590822359207240000000000000)
      linear := (-17341026409689141641618654196367500000000000)
      constant := (447704340850371483005889969725139142406517340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree079.table
  base := (-149377153297511145075448225275033641701/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-35096142078325187590379098150575000000000000)
      constant := (917283590572085536313016076226527286902218275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree079.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66645397382737899027/25000000000000000000)
  centralHi := (266581589530951596109/100000000000000000000)
  directionLo := (268285003601247122797/100000000000000000000)
  directionHi := (134142501800623561399/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree080.table
  base := (-1489566002873452806243854698789301838613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-70223733973785583102819598054910000000000000)
      constant := (1836322259152496059358292910956126305012725015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree080.table
  base := (-7447830602366598352567976985905830440857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-71062395764057794357790311488510000000000000)
      constant := (1881174996418042059360863052683339758980238567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree080.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268285003601247122797/100000000000000000000)
  centralHi := (134142501800623561399/50000000000000000000)
  directionLo := (269977670257733725909/100000000000000000000)
  directionHi := (26997767025773372591/10000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree081.table
  base := (-1856055120241194018340452793759932280427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (2009)
      previous := (0)
      next := (1078)
      square := (18345726662204621202484356360000000000000)
      linear := (-1974537841911516656643460536787500000000000)
      constant := (52288801275749227245229944403424369864331693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree081.table
  base := (-3712110479699054296661231754401496009963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (4067)
      previous := (0)
      next := (2107)
      square := (36691453324409242404968712720000000000000)
      linear := (-3996250409525845196379023704215000000000000)
      constant := (107131457261723187047915475788686440259606317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree081.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269977670257733725909/100000000000000000000)
  centralHi := (26997767025773372591/10000000000000000000)
  directionLo := (271659790396492100529/100000000000000000000)
  directionHi := (27165979039649210053/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree082.table
  base := (-7398028538546475482741536644164634050529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-71942990643843616175509560593790000000000000)
      constant := (1929041122945311263875637485093810567453450399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree082.table
  base := (-3699014463885475820172637700389478549057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-36401309489436316355927270931615000000000000)
      constant := (988070441630919683623617330130189159638792767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree082.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271659790396492100529/100000000000000000000)
  centralHi := (27165979039649210053/10000000000000000000)
  directionLo := (273331558731768918493/100000000000000000000)
  directionHi := (136665779365884459247/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree083.table
  base := (-736925437381218161433268410152414183669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-36401309489436316355927270931615000000000000)
      constant := (988127544733250862740239317563560340525088695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree083.table
  base := (-3684627345207428155981596792175116157307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36603)
      previous := (0)
      next := (18963)
      square := (330223079919683181644718414480000000000000)
      linear := (-36836365293140025944443328525295000000000000)
      constant := (1012249476672229983417596173696969463971648517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree083.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273331558731768918493/100000000000000000000)
  centralHi := (136665779365884459247/50000000000000000000)
  directionLo := (137496582029527975583/50000000000000000000)
  directionHi := (274993164059055951167/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree084.table
  base := (-1467579632978860625104662553847160147189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (164)
      previous := (0)
      next := (88)
      square := (1497610339771805812447702560000000000000)
      linear := (-167034574407940247728343589870000000000000)
      constant := (4589657017649741577509361091996877793376495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree084.table
  base := (-3668949211193906368799745873195807310811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (83)
      previous := (0)
      next := (43)
      square := (748805169885902906223851280000000000000)
      linear := (-84515694097151327739136929975000000000000)
      constant := (2350839501433190479368107315571237734202701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree084.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137496582029527975583/50000000000000000000)
  centralHi := (274993164059055951167/100000000000000000000)
  directionLo := (11065791580157889943/4000000000000000000)
  directionHi := (4322574835999175759/1562500000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree085.table
  base := (-7303960082314183537902896770219848514703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (72324)
      previous := (0)
      next := (38808)
      square := (660446159839366363289436828960000000000000)
      linear := (-74521875648930665784544504402110000000000000)
      constant := (2072392088219614982041897681630447421245143793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree085.table
  base := (-7303960291704578724497544881744137486419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-75412953801094890242950887425310000000000000)
      constant := (2122965343353830901412720619725532518316402989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree085.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11065791580157889943/4000000000000000000)
  centralHi := (4322574835999175759/1562500000000000000)
  directionLo := (69571653189425730081/25000000000000000000)
  directionHi := (11131464510308116813/4000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree086.table
  base := (-726744028977678387791511290536943364713/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (36162)
      previous := (0)
      next := (19404)
      square := (330223079919683181644718414480000000000000)
      linear := (-37690751991979841160444742835775000000000000)
      constant := (1060657559562496787123666001041924358927270515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree086.table
  base := (-7267440460026904793597842480455747632503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (73206)
      previous := (0)
      next := (37926)
      square := (660446159839366363289436828960000000000000)
      linear := (-76283065408502309419983002612670000000000000)
      constant := (2173073661972095174847729446783041137646595593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree086.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69571653189425730081/25000000000000000000)
  centralHi := (11131464510308116813/4000000000000000000)
  directionLo := (27991880630037725601/10000000000000000000)
  directionHi := (279918806300377256011/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree087.table
  base := (-361416947241708922251066119269866007211/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (2009)
      previous := (0)
      next := (1078)
      square := (18345726662204621202484356360000000000000)
      linear := (-2117809231083019412700957415027500000000000)
      constant := (60300217690954100816760251674597445454099745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree087.table
  base := (-1445667816648340139652568158197019987167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (8134)
      previous := (0)
      next := (4214)
      square := (73382906648818484809937425440000000000000)
      linear := (-8572575223989969844112790866670000000000000)
      constant := (247085043944461297588511282739580570928296765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree087.checked
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
end ForestUnimodality.Stage170KernelData.Cell325.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell325
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 87 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 87 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 87 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel087.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell325

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel088
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  degreePropagationTail 88 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel089
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  degreePropagationTail 89 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel090
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  degreePropagationTail 90 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel091
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  degreePropagationTail 91 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel092
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  degreePropagationTail 92 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel093
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  degreePropagationTail 93 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel094
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  degreePropagationTail 94 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel095
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  degreePropagationTail 95 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel096
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  degreePropagationTail 96 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel097
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  degreePropagationTail 97 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel098
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  degreePropagationTail 98 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel099
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  degreePropagationTail 99 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel100
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  degreePropagationTail 100 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel101
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  degreePropagationTail 101 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel102
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  degreePropagationTail 102 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel103
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  degreePropagationTail 103 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel104
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  degreePropagationTail 104 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel105
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  degreePropagationTail 105 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel106
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  degreePropagationTail 106 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel107
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  degreePropagationTail 107 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel108
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  degreePropagationTail 108 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel109
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  degreePropagationTail 109 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel110
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  degreePropagationTail 110 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel111
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  degreePropagationTail 111 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel112
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  degreePropagationTail 112 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel113
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  degreePropagationTail 113 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel114
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  degreePropagationTail 114 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel115
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  degreePropagationTail 115 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel116
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  degreePropagationTail 116 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel117
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  degreePropagationTail 117 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel118
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  degreePropagationTail 118 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel119
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  degreePropagationTail 119 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel120
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  degreePropagationTail 120 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel121
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  degreePropagationTail 121 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel122
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  degreePropagationTail 122 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel123
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  degreePropagationTail 123 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel124
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  degreePropagationTail 124 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel125
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  degreePropagationTail 125 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel126
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  degreePropagationTail 126 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel127
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  degreePropagationTail 127 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell325.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 87 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell325.Kernel349

