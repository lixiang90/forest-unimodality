import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell006.Parameters
import ForestUnimodality.BinomialMassData.Q37_126.Batch000_049
import ForestUnimodality.BinomialMassData.Q37_126.Batch050_099
import ForestUnimodality.BinomialMassData.Q37_126.Batch100_149
import ForestUnimodality.BinomialMassData.Q19_63.Batch000_049
import ForestUnimodality.BinomialMassData.Q19_63.Batch050_099
import ForestUnimodality.BinomialMassData.Q19_63.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree000.table
  base := (597996435890083699981278893/100000000000000000000000000)
  polynomial :=
    { denominator := 63000000000000000000000000000000000000000
      center := (89)
      previous := (37)
      next := (0)
      square := (1254917169972805505301360918000000000000)
      linear := (2007958220188799346173080809000000000000)
      constant := (376737754610752730988205702590000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree000.table
  base := (597996435890083699981278893/100000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (627458584986402752650680459000000000000)
      linear := (1003979110094399673086540404500000000000)
      constant := (188368877305376365494102851295000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree001.table
  base := (21253055210158154457246648931884826152683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (400347162914502775563768685005000000000000)
      constant := (84201726930371139409559938903610874999998827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree001.table
  base := (10511162552205840655852964401716222600151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (197036288532319374018630940207500000000000)
      constant := (41641403340688877990463138470849187499999319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (7248455080507928537/25000000000000000000)
  directionHi := (28993820322031714149/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree002.table
  base := (30105331036058207649019963930397762345679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (336374972939067514166033830350000000000000)
      constant := (119017809833612276867028191082758718749999951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree002.table
  base := (14725332893836281015833023217882412918871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (155638314769805702030003305995000000000000)
      constant := (58207151685343242646675936588985296874998999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/25000000000000000000)
  centralHi := (28993820322031714149/100000000000000000000)
  directionLo := (820069078488518167/2000000000000000000)
  directionHi := (41003453924425908351/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree003.table
  base := (4236635563131013831259851727356492956649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1246)
      previous := (518)
      next := (0)
      square := (17568840379619277074219052852000000000000)
      linear := (-2843208443352678284343771318000000000000)
      constant := (1857226239940137230957059655570213393882209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree003.table
  base := (20485712335226248197653006222990501605823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-18399099450006076439390059650000000000000)
      constant := (8978937198327609081877790355228811208167943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (820069078488518167/2000000000000000000)
  centralHi := (41003453924425908351/100000000000000000000)
  directionLo := (50218769903281956403/100000000000000000000)
  directionHi := (12554692475820489101/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree004.table
  base := (147352921214667327527161487306154066683/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5607)
      previous := (2331)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-59226373284080855975697324897000000000000)
      constant := (5808926731903017664397029108251254906648270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree004.table
  base := (7036879643999974140894419843455423315521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-321230209819860389984513842845000000000000)
      constant := (27741621149535814296094392814934575139302849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50218769903281956403/100000000000000000000)
  centralHi := (12554692475820489101/25000000000000000000)
  directionLo := (7248455080507928537/12500000000000000000)
  directionHi := (57987640644063428297/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree005.table
  base := (2512047908803116080888622098626920562839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-528291542865373298359238394315000000000000)
      constant := (19864129038764023459213814039550495427815982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree005.table
  base := (9458840989112538278954278461059676084977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-1119328944229386871983544834530000000000000)
      constant := (37432298220894744682899514329895854381273713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/12500000000000000000)
  centralHi := (57987640644063428297/100000000000000000000)
  directionLo := (64832153167477756241/100000000000000000000)
  directionHi := (32416076583738878121/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree006.table
  base := (665008404880126665229693431502098047599/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441000000000000000000000000000000000000000
      center := (623)
      previous := (259)
      next := (0)
      square := (8784420189809638537109526426000000000000)
      linear := (-16898915984674273707555336981000000000000)
      constant := (295773437799851314045359554215425238991159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree006.table
  base := (6144885703506131614588465441507542206213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-177355274313228107110895775930000000000000)
      constant := (2743188203774786466066695272404826112939933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64832153167477756241/100000000000000000000)
  centralHi := (32416076583738878121/50000000000000000000)
  directionLo := (71020065482915145463/100000000000000000000)
  directionHi := (8877508185364393183/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree007.table
  base := (4152909436910793281657753858418214827897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8010)
      previous := (3330)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-283603113072946095805926266850000000000000)
      constant := (2460444492685928227423916237153127807417599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree007.table
  base := (3730714139687837938940775772534804965519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7920)
      previous := (3420)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-296152284772674150858939876030000000000000)
      constant := (2237164075767335332732969277537234415449273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71020065482915145463/100000000000000000000)
  centralHi := (8877508185364393183/12500000000000000000)
  directionLo := (38355219064893288933/50000000000000000000)
  directionHi := (76710438129786577867/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree008.table
  base := (57464397680877060875977885282961340013/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5607)
      previous := (2331)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-244954114440056070760298740761000000000000)
      constant := (1051439749741032261076599574764294234046388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree008.table
  base := (6099384439159823229867317883524377533/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1984500000000000000000000000000000000000000
      center := (2772)
      previous := (1197)
      next := (0)
      square := (39529890854143373416992868917000000000000)
      linear := (-127496725899919257401354814052500000000000)
      constant := (464838471158720937052424478863332070855632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38355219064893288933/50000000000000000000)
  centralHi := (76710438129786577867/100000000000000000000)
  directionLo := (820069078488518167/1000000000000000000)
  directionHi := (82006907848851816701/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree009.table
  base := (905034333178986972252462020493093542103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-323762277476722082729387883030000000000000)
      constant := (641212729372994924563302621637454252067423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree009.table
  base := (124711040172703356163280162914846991193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1232)
      previous := (532)
      next := (0)
      square := (17568840379619277074219052852000000000000)
      linear := (-67262289835290027556480298442000000000000)
      constant := (108130898737611458460226992931447523116113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (820069078488518167/1000000000000000000)
  centralHi := (82006907848851816701/100000000000000000000)
  directionLo := (21745365241523785611/25000000000000000000)
  directionHi := (17396292193219028489/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree010.table
  base := (-157380276749540451895403087437800004201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-3378179850180436781525994486930000000000000)
      constant := (2478022298409456809806799207809371783326231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree010.table
  base := (-384090717689814641727071436865342150063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-3503671567177717332056130578730000000000000)
      constant := (1851297900276165459634039475981457006399953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21745365241523785611/25000000000000000000)
  centralHi := (17396292193219028489/20000000000000000000)
  directionLo := (91686510287296855559/100000000000000000000)
  directionHi := (2292162757182421389/2500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree011.table
  base := (-981079424012515914140250428795285205091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-3842499203070374818487498026590000000000000)
      constant := (268939450265088268412949407581513020993821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree011.table
  base := (-290709710754375163406905765534331449539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-995135022941845856017661931892500000000000)
      constant := (-27745452446170726498207743443261523220291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91686510287296855559/100000000000000000000)
  centralHi := (2292162757182421389/2500000000000000000)
  directionLo := (96161623247160565677/100000000000000000000)
  directionHi := (48080811623580282839/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree012.table
  base := (-1631982546365937516379912935918298735783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-478535395106701428383222396250000000000000)
      constant := (-124218692058856418838258301599969742480303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree012.table
  base := (-1777414119597171984733559069319952054257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-495267624039672168453907208490000000000000)
      constant := (-141982443513527314770924360490098855927337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96161623247160565677/100000000000000000000)
  centralHi := (48080811623580282839/50000000000000000000)
  directionLo := (100437539806563912807/100000000000000000000)
  directionHi := (12554692475820489101/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree013.table
  base := (-2157165322892605773556456670685452396141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-4771137908850250892410505105910000000000000)
      constant := (-1869544108254566547870083357730560560283629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree013.table
  base := (-568389852831859359378106017531820840553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-1233569285236678902024920506312500000000000)
      constant := (-457709018012150414549027474956296916154857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100437539806563912807/100000000000000000000)
  centralHi := (12554692475820489101/12500000000000000000)
  directionLo := (26134676460668794933/25000000000000000000)
  directionHi := (104538705842675179733/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree014.table
  base := (-1295147109331661285623356258234795803899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (4005)
      previous := (1665)
      next := (0)
      square := (56471272648776247738561241310000000000000)
      linear := (-373961232981442066383714903255000000000000)
      constant := (-151386456341107196458483449894129220810733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree014.table
  base := (-2683655327803818161707347499270995543861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7920)
      previous := (3420)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-773020809362340242873457024870000000000000)
      constant := (-271211812935696260728097666626654473369187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26134676460668794933/25000000000000000000)
  centralHi := (104538705842675179733/100000000000000000000)
  directionLo := (108484941978726379241/100000000000000000000)
  directionHi := (54242470989363189621/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree015.table
  base := (-2955488090918224438795063161845456813691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-633308512736680774037056909470000000000000)
      constant := (-218143868275401362462026047523846454837731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree015.table
  base := (-3030669747185993459560028898318177342897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-654223798902894199125412924770000000000000)
      constant := (-174660150615703276026371780508316208217577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108484941978726379241/100000000000000000000)
  centralHi := (54242470989363189621/50000000000000000000)
  directionLo := (112292583250158993679/100000000000000000000)
  directionHi := (1403657290626987421/1250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree016.table
  base := (-817515640524151674122805286819127167079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-3082047983760032501647507862445000000000000)
      constant := (-734961545412732104659175409210231452273102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree016.table
  base := (-832733520498503299949559346222688542037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-1591220678678928471035808367942500000000000)
      constant := (-229007860828761641149653150557850823344853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112292583250158993679/100000000000000000000)
  centralHi := (1403657290626987421/1250000000000000000)
  directionLo := (7248455080507928537/6250000000000000000)
  directionHi := (115975281288126856593/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree017.table
  base := (-3546480933908588802465509123549837216857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-6628415320410003040256519264550000000000000)
      constant := (-688762062303520721218368071609303913705433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree017.table
  base := (-449511935400402402841486882457678252363/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-1710437809826344994039437655152500000000000)
      constant := (5754875976960792407358945768450032742506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/6250000000000000000)
  centralHi := (115975281288126856593/100000000000000000000)
  directionLo := (119544583677916611033/100000000000000000000)
  directionHi := (59772291838958305517/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree018.table
  base := (-4742176976828512645371423336493141461/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 441000000000000000000000000000000000000000
      center := (623)
      previous := (259)
      next := (0)
      square := (8784420189809638537109526426000000000000)
      linear := (-78808163036666011969089142269000000000000)
      constant := (3827485780900317599686922861521969255920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree018.table
  base := (-239655638601990165249218450604536823121/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1540)
      previous := (665)
      next := (0)
      square := (21961050474524096342773816065000000000000)
      linear := (-203294993441529057449229660262500000000000)
      constant := (33670134531271678347923535418597044014556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119544583677916611033/100000000000000000000)
  centralHi := (59772291838958305517/50000000000000000000)
  directionLo := (2460207235465554501/2000000000000000000)
  directionHi := (123010361773277725051/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree019.table
  base := (-4018365092374887156761452032175262557393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-7557054026189879114179526343870000000000000)
      constant := (1603904044681801743232889186846382909707183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree019.table
  base := (-4052110415812462359183858243206572726781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-7795488288484712160186784918290000000000000)
      constant := (2627501808254959551377723673283112847406211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2460207235465554501/2000000000000000000)
  centralHi := (123010361773277725051/100000000000000000000)
  directionLo := (63190566385456075119/50000000000000000000)
  directionHi := (126381132770912150239/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree020.table
  base := (-211254853250682327090956918368357871867/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5607)
      previous := (2331)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-802137337907981715114102988353000000000000)
      constant := (307069363097292590987885506061975213119754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree020.table
  base := (-4253285096573720536223624913858022108827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-8272356813074378252201302067130000000000000)
      constant := (4251968523564499797781283826697510250065637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63190566385456075119/50000000000000000000)
  centralHi := (126381132770912150239/100000000000000000000)
  directionLo := (64832153167477756241/50000000000000000000)
  directionHi := (129664306334955512483/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree021.table
  base := (-4417408861626629012481212316410509209741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (890)
      previous := (370)
      next := (0)
      square := (12549171699728055053013609180000000000000)
      linear := (-134693535428091352192103705130000000000000)
      constant := (75096264164982728299000056606137919786317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree021.table
  base := (-555145045435773272436031685254109765083/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3137292924932013763253402295000000000000)
      linear := (-34719148165333509302443727047500000000000)
      constant := (24099357555487352306928253570482169599542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64832153167477756241/50000000000000000000)
  centralHi := (129664306334955512483/100000000000000000000)
  directionLo := (132866376311659239359/100000000000000000000)
  directionHi := (415207425973935123/312500000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree022.table
  base := (-919570949400004561448832921729782853443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11214)
      previous := (4662)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-1790002416971938645012807392570000000000000)
      constant := (1314975840401675708702952599756491854684733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree022.table
  base := (-2309019194010479337541750218033842872041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-4613046931126855218115168182405000000000000)
      constant := (4040786615470552519308942195133677640869271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132866376311659239359/100000000000000000000)
  centralHi := (415207425973935123/312500000000000000)
  directionLo := (13599307177594637549/10000000000000000000)
  directionHi := (135993071775946375491/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree023.table
  base := (-2384163451573518836444185090183188401337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-4707165718874815631012770251255000000000000)
      constant := (4297313619702948203470412618147925235093447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree023.table
  base := (-4785617047880847420885223877131028698699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-9702962386843376528244853513650000000000000)
      constant := (10270835027836926069427896494676947094863669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13599307177594637549/10000000000000000000)
  centralHi := (135993071775946375491/100000000000000000000)
  directionLo := (139049477481664640317/100000000000000000000)
  directionHi := (69524738740832320159/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree024.table
  base := (-4930237786122754099044913808653282029309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-1097627865626618810998560449130000000000000)
      constant := (1198300301833761223307712755383902625074731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree024.table
  base := (-2472579815593817450631542887678730608341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3080)
      previous := (1330)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-565546161746280145569965036805000000000000)
      constant := (701989416895273399628487102973679801721619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139049477481664640317/100000000000000000000)
  centralHi := (69524738740832320159/50000000000000000000)
  directionLo := (142040130965830290927/100000000000000000000)
  directionHi := (8877508185364393183/6250000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree025.table
  base := (-5084650755787824899948496448634579959363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-10342970143529507335948547581830000000000000)
      constant := (13140885158015311332303003594369352141288253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree025.table
  base := (-2548807635785849116209290697224139373721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-5328349718011354356136943905665000000000000)
      constant := (7586364774198061818034381882592390825701351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142040130965830290927/100000000000000000000)
  centralHi := (8877508185364393183/6250000000000000000)
  directionLo := (7248455080507928537/5000000000000000000)
  directionHi := (144969101610158570741/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree026.table
  base := (-5232373850416545755770395586443131501387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-10807289496419445372910051121490000000000000)
      constant := (15659967460029597819941791281577211070994997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree026.table
  base := (-2621852319528558756643372694048565092727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-5566783980306187402144202480085000000000000)
      constant := (8939367410677479742511365844571245146966537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/5000000000000000000)
  centralHi := (144969101610158570741/100000000000000000000)
  directionLo := (147840055595642751097/100000000000000000000)
  directionHi := (73920027797821375549/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree027.table
  base := (-1343506819153564051751348908844160103223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-626200491628299078326197481175000000000000)
      constant := (1018860445696117657581221029094450788957314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree027.table
  base := (-43071848801680788163710188831408304851/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1232)
      previous := (532)
      next := (0)
      square := (17568840379619277074219052852000000000000)
      linear := (-258009699671156464362287157978000000000000)
      constant := (461147311357559066952541562359723439017725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147840055595642751097/100000000000000000000)
  centralHi := (73920027797821375549/50000000000000000000)
  directionLo := (15065630970984586921/10000000000000000000)
  directionHi := (150656309709845869211/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree028.table
  base := (-2755046065446719879113693628915131157187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (4005)
      previous := (1665)
      next := (0)
      square := (56471272648776247738561241310000000000000)
      linear := (-838280585871380103345218442915000000000000)
      constant := (1512681240961344596586413805835120633874971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree028.table
  base := (-1379718633290043701119450155469876721551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1417500000000000000000000000000000000000000
      center := (1980)
      previous := (855)
      next := (0)
      square := (28235636324388123869280620655000000000000)
      linear := (-431689464635418106725622830637500000000000)
      constant := (849632354689485734198125481018579898880583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15065630970984586921/10000000000000000000)
  centralHi := (150656309709845869211/100000000000000000000)
  directionLo := (38355219064893288933/25000000000000000000)
  directionHi := (153420876259573155733/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree029.table
  base := (-564094570039633335676843795007148322311/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5607)
      previous := (2331)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-1220024755508925948379456174047000000000000)
      constant := (2417261806014817892322425966286628308747641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree029.table
  base := (-5648722856211170196142875962184905586521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-12564173534381373080331956406690000000000000)
      constant := (26991624384253410334571198630358109727098151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38355219064893288933/25000000000000000000)
  centralHi := (153420876259573155733/100000000000000000000)
  directionLo := (78068250411293189741/50000000000000000000)
  directionHi := (156136500822586379483/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree030.table
  base := (-5766887149709808349808987510514534539243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-1407174100886577502306229475570000000000000)
      constant := (3035949188705876574727356900813090268193837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree030.table
  base := (-1154758966864553725803883694204377062103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1232)
      previous := (532)
      next := (0)
      square := (17568840379619277074219052852000000000000)
      linear := (-289800934643800870496588301234000000000000)
      constant := (674584836484635595814091630915869715612577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78068250411293189741/50000000000000000000)
  centralHi := (156136500822586379483/100000000000000000000)
  directionLo := (79402847093142347173/50000000000000000000)
  directionHi := (158805694186284694347/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree031.table
  base := (-92002442283853265914793692604148147287/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-6564443130434567778858784409895000000000000)
      constant := (15314679706694646524050869818517352109372704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree031.table
  base := (-2947153338661643911060338790338574015911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-6758955291780352632180495352185000000000000)
      constant := (16941463783581290980986350377171199730849241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79402847093142347173/50000000000000000000)
  centralHi := (158805694186284694347/100000000000000000000)
  directionLo := (8071537976565252397/5000000000000000000)
  directionHi := (161430759531305047941/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree032.table
  base := (-6004947478078764901295148886594297710143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-13593205613759073594679072359450000000000000)
      constant := (34089296995566945312325416118867232388442433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree032.table
  base := (-3005217102529609766834724480246135163349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-6997389554075185678187753926605000000000000)
      constant := (18785378165672312498600327354063089536667819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8071537976565252397/5000000000000000000)
  centralHi := (161430759531305047941/100000000000000000000)
  directionLo := (820069078488518167/500000000000000000)
  directionHi := (164013815697703633401/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree033.table
  base := (-3058709843592454022087212212273613797767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-780973609258278423980031994395000000000000)
      constant := (2094595793755845298564747576227336315184753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree033.table
  base := (-1530580458744439665918925252657813729407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1540)
      previous := (665)
      next := (0)
      square := (21961050474524096342773816065000000000000)
      linear := (-401990212020556595788611805612500000000000)
      constant := (1150534187264078176643845018675404145331513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (820069078488518167/500000000000000000)
  centralHi := (164013815697703633401/100000000000000000000)
  directionLo := (166556817202378582213/100000000000000000000)
  directionHi := (83278408601189291107/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree034.table
  base := (-1556426075762866508454682585072678343251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-7260922159769474834301039719385000000000000)
      constant := (20734559941847476071135544063518079311273562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree034.table
  base := (-1557522320431467392231079997401557338281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-3737129039332425885101135537722500000000000)
      constant := (11356968912553837128956696271718218924362711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166556817202378582213/100000000000000000000)
  centralHi := (83278408601189291107/50000000000000000000)
  directionLo := (16906157154555500351/10000000000000000000)
  directionHi := (169061571545555003511/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree035.table
  base := (-6329910787001733489153048510234628379553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8010)
      previous := (3330)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-2140880524632698243651940425490000000000000)
      constant := (6484007047406285610589865473746965708793449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree035.table
  base := (-3166918300251016738237007155729421065347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (3960)
      previous := (1710)
      next := (0)
      square := (56471272648776247738561241310000000000000)
      linear := (-1101813191565669259458504235695000000000000)
      constant := (3542592424170532534067838161176418255948251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16906157154555500351/10000000000000000000)
  centralHi := (169061571545555003511/100000000000000000000)
  directionLo := (34305950848398924639/20000000000000000000)
  directionHi := (42882438560498655799/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree036.table
  base := (-6430131053531922390464433654742575910073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-1716720336146536193613898502010000000000000)
      constant := (5495460869268543491108894083838524023657807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree036.table
  base := (-3216824012004878303869364778273753993637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3080)
      previous := (1330)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-883458511472724206912976469365000000000000)
      constant := (2995786182579051058319739898481274488806083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34305950848398924639/20000000000000000000)
  centralHi := (42882438560498655799/25000000000000000000)
  directionLo := (21745365241523785611/12500000000000000000)
  directionHi := (173962921932190284889/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree037.table
  base := (-1631610703702154893076882376023344092347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-7957401189104381889743295028875000000000000)
      constant := (26841053459412222716738336238256694594949514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree037.table
  base := (-6529594914393059850561302747705935760849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-16379121731098701816448093597410000000000000)
      constant := (58411164457972120330395316691825140965190319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21745365241523785611/12500000000000000000)
  centralHi := (173962921932190284889/100000000000000000000)
  directionLo := (17636252386505357237/10000000000000000000)
  directionHi := (176362523865053572371/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree038.table
  base := (-66189121721849951902982401481550225733/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5607)
      previous := (2331)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-1637912173109870181644809359741000000000000)
      constant := (5805666426179592896697941214944271540657230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree038.table
  base := (-1324347612130541889352078566199575330751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11088)
      previous := (4788)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-3371198051137673581692522149250000000000000)
      constant := (12611418436298203621018294491405885512249281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17636252386505357237/10000000000000000000)
  centralHi := (176362523865053572371/100000000000000000000)
  directionLo := (44682477998174694219/25000000000000000000)
  directionHi := (178729911992698776877/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree039.table
  base := (-3353797822988415091574950967068188092317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-935746726888257769633866507615000000000000)
      constant := (3476810862399889304151946322847929051288203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree039.table
  base := (-1342025897525506202956333929810818018563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1232)
      previous := (532)
      next := (0)
      square := (17568840379619277074219052852000000000000)
      linear := (-385174639561734088899491731002000000000000)
      constant := (1508038399342095855427398263619429253813717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44682477998174694219/25000000000000000000)
  centralHi := (178729911992698776877/100000000000000000000)
  directionLo := (181066349877010856143/100000000000000000000)
  directionHi := (11316646867313178509/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree040.table
  base := (-6792541782660731646132813992309451025251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-17307760436878577890371100676730000000000000)
      constant := (67259708022065027395615720213923788880778781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree040.table
  base := (-1698703474215962503826135147910780179813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-4452431826216925023122911260982500000000000)
      constant := (18206223601061160186095774244842113466322203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181066349877010856143/100000000000000000000)
  centralHi := (11316646867313178509/6250000000000000000)
  directionLo := (183373020574593711119/100000000000000000000)
  directionHi := (2292162757182421389/1250000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree041.table
  base := (-6873792441268207764961220111580913639841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-17772079789768515927332604216390000000000000)
      constant := (72087835619900932740521637759255353763471071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree041.table
  base := (-6714677565522634721384436433965123233/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-4571648957364341546126540548192500000000000)
      constant := (19486609630702173171691199295697161027385088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183373020574593711119/100000000000000000000)
  centralHi := (2292162757182421389/1250000000000000000)
  directionLo := (92825516819887175493/50000000000000000000)
  directionHi := (185651033639774350987/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree042.table
  base := (-1737845958459427446787338049646004136337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (445)
      previous := (185)
      next := (0)
      square := (6274585849864027526506804590000000000000)
      linear := (-144733326529035348922969109175000000000000)
      constant := (611641544374008813556101587379603478821538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree042.table
  base := (-3476605299375378973588724931808108610471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6274585849864027526506804590000000000000)
      linear := (-148916383762278033940640312235000000000000)
      constant := (660525619661133360325818081166089157540327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92825516819887175493/50000000000000000000)
  centralHi := (185651033639774350987/100000000000000000000)
  directionLo := (93950715681657911089/50000000000000000000)
  directionHi := (187901431363315822179/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree043.table
  base := (-3512673687678390930732287133582840063057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-9350359247774196000627805647855000000000000)
      constant := (41098290124825998985899769597344707789726767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree043.table
  base := (-7026985090187104314694092333034717089263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-19240332878636698368535196490450000000000000)
      constant := (88664148449529967543427632526195207872715153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93950715681657911089/50000000000000000000)
  centralHi := (187901431363315822179/100000000000000000000)
  directionLo := (38025038869276200191/20000000000000000000)
  directionHi := (47531298586595250239/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree044.table
  base := (-443481899034184362634788584573248985207/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-9582518924219165019108557417685000000000000)
      constant := (43738482083737929587478336416280198221707336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree044.table
  base := (-1419435676255368502752198113745893394399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11088)
      previous := (4788)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-3943440280645272892109942727858000000000000)
      constant := (18852020019495146935397354896006549117630369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38025038869276200191/20000000000000000000)
  centralHi := (47531298586595250239/25000000000000000000)
  directionLo := (96161623247160565677/50000000000000000000)
  directionHi := (38464649298864226271/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree045.table
  base := (-7162496666597716852423183823999915312207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-2181039689036474230575402041670000000000000)
      constant := (10323099095755506193920946691916037347316713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree045.table
  base := (-2798364176267413001508295481842970379/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 220500000000000000000000000000000000000000
      center := (308)
      previous := (133)
      next := (0)
      square := (4392210094904819268554763213000000000000)
      linear := (-112189277376755725292023504378500000000000)
      constant := (555633313447986936615122847138428008046208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96161623247160565677/50000000000000000000)
  centralHi := (38464649298864226271/20000000000000000000)
  directionLo := (194496459502433268723/100000000000000000000)
  directionHi := (48624114875608317181/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree046.table
  base := (-722572700146197893857201533384228270009/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5607)
      previous := (2331)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-2009367655421820611214012191469000000000000)
      constant := (9848928085699004375127965475324997996334279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree046.table
  base := (-903363228907244283490924523984373042843/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-5167734613101424161144686984242500000000000)
      constant := (26481440490922830931958572759287046785912266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194496459502433268723/100000000000000000000)
  centralHi := (48624114875608317181/25000000000000000000)
  directionLo := (196645656895462412259/100000000000000000000)
  directionHi := (9832282844773120613/5000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree047.table
  base := (-728541955581227968428244100899174114759/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5607)
      previous := (2331)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-2055799590710814414910162545435000000000000)
      constant := (10422105904952399755054681910832177938521529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree047.table
  base := (-1457295117518128150319664381454469819607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11088)
      previous := (4788)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-4229561395399072547318653017162000000000000)
      constant := (22399066179143314926324541259361209285979817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196645656895462412259/100000000000000000000)
  centralHi := (9832282844773120613/5000000000000000000)
  directionLo := (6211613052310562617/3125000000000000000)
  directionHi := (39754323534787600749/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree048.table
  base := (-3670795116337486873574762825417815879459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-1167906403333226788114618277445000000000000)
      constant := (6116842406682767528171955616430743197158581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree048.table
  base := (-7342536047696336549837842801743076435217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-2402741722398336536511975803850000000000000)
      constant := (13135849524001074081832880009071303292069303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6211613052310562617/3125000000000000000)
  centralHi := (39754323534787600749/20000000000000000000)
  directionLo := (100437539806563912807/50000000000000000000)
  directionHi := (40175015922625565123/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree049.table
  base := (-3697126484856875679421060448331525824833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (4005)
      previous := (1665)
      next := (0)
      square := (56471272648776247738561241310000000000000)
      linear := (-1534759615206287158787473752405000000000000)
      constant := (8295395596478593649387937754796024857319689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree049.table
  base := (-7395099878931305008187106310184745442783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7920)
      previous := (3420)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-3157363432310670702946042769070000000000000)
      constant := (17801093735404798689143016888935249333942039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100437539806563912807/50000000000000000000)
  centralHi := (40175015922625565123/20000000000000000000)
  directionLo := (50739185563555499759/25000000000000000000)
  directionHi := (202956742254221999037/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree050.table
  base := (-3721709997421469169196953819512605236353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-10975476982888979129993068036665000000000000)
      constant := (61159067804081762563904961029979469816914943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree050.table
  base := (-3722089083848536989340945842433756072481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-11289206275382180506318408266165000000000000)
      constant := (65575159094630341424704146433630422148322911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50739185563555499759/25000000000000000000)
  centralHi := (202956742254221999037/100000000000000000000)
  directionLo := (205017269622129541751/100000000000000000000)
  directionHi := (25627158702766192719/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree051.table
  base := (-7489102046111917802068197623164602712791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-2490585924296432921883071068110000000000000)
      constant := (14294545830373495114198055250814410203659169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree051.table
  base := (-7489780625273586796763585870794719220709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-2561697897261558567183481520130000000000000)
      constant := (15316732588468983079372286581229528823667331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205017269622129541751/100000000000000000000)
  centralHi := (25627158702766192719/12500000000000000000)
  directionLo := (103528646349910346719/50000000000000000000)
  directionHi := (207057292699820693439/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree052.table
  base := (-1506261712293811807472364087211708521163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11214)
      previous := (4662)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-4575918534311566866781828630530000000000000)
      constant := (27026766297415405217854787505708728879504053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree052.table
  base := (-470744735340848476011926412683757558789/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-5883037399985923299166462707502500000000000)
      constant := (36177111919367682875139990004962664996665836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103528646349910346719/50000000000000000000)
  centralHi := (207057292699820693439/100000000000000000000)
  directionLo := (41815482337070071893/20000000000000000000)
  directionHi := (104538705842675179733/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree053.table
  base := (-946255980372668361731174204520997098561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-11671956012223886185435323346155000000000000)
      constant := (70883429849203186222161292892034650063245564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree053.table
  base := (-118290485284111889471101823740515174013/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-6002254531133339822170091994712500000000000)
      constant := (37930962921198545496613392560309824389478448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41815482337070071893/20000000000000000000)
  centralHi := (104538705842675179733/50000000000000000000)
  directionLo := (211078198054445543089/100000000000000000000)
  directionHi := (21107819805444554309/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree054.table
  base := (-7605327199278128594499684921867686959311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-2645359041926412267536905581330000000000000)
      constant := (16505552011044401773885044781006350050943849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree054.table
  base := (-7605813062697998505960374562795232741911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-2720654072124780597854987236410000000000000)
      constant := (17655197698287209042657714824587302360817249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211078198054445543089/100000000000000000000)
  centralHi := (21107819805444554309/10000000000000000000)
  directionLo := (21306019644874543639/10000000000000000000)
  directionHi := (213060196448745436391/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree055.table
  base := (-381857653467422572018113391639300121071/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5607)
      previous := (2331)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-2427255073022764844479365377163000000000000)
      constant := (15548313113370922791333663188472235638938402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree055.table
  base := (-7637587543072453082738084878749590105927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-24962755173712691472709402276530000000000000)
      constant := (166227207599231676091027442928692876869575737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21306019644874543639/10000000000000000000)
  centralHi := (213060196448745436391/100000000000000000000)
  directionLo := (215023926407375085577/100000000000000000000)
  directionHi := (107511963203687542789/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree056.table
  base := (-7665531130310688058870213514495196293099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8010)
      previous := (3330)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-3533838583302512354536451044470000000000000)
      constant := (23223760895550341047307773282041223701812867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree056.table
  base := (-1533183913727490631871399637263448782741/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1134000000000000000000000000000000000000000
      center := (1584)
      previous := (684)
      next := (0)
      square := (22588509059510499095424496524000000000000)
      linear := (-726846391380067358992111983582000000000000)
      constant := (4963289043101717453710664872951624540185853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215023926407375085577/100000000000000000000)
  centralHi := (107511963203687542789/50000000000000000000)
  directionLo := (216969883957452758483/100000000000000000000)
  directionHi := (54242470989363189621/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree057.table
  base := (-3845233195680304786769632192830624146999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-1400066079778195806595370047275000000000000)
      constant := (9433307423518393257176931368781694751173441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree057.table
  base := (-7690813601345947280760210581309006102913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-2879610246988002628526492952690000000000000)
      constant := (20151165367008770330619751987872728308615367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216969883957452758483/100000000000000000000)
  centralHi := (54242470989363189621/25000000000000000000)
  directionLo := (21889854307732789271/10000000000000000000)
  directionHi := (218898543077327892711/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree058.table
  base := (-3855981637883801538245829246320399335841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-12832754394448731277839082195305000000000000)
      constant := (88591367820594552219397262035039335036047071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree058.table
  base := (-7712273571854711576457369997862085407977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-26393360747481689748752953723050000000000000)
      constant := (189163307382011397920117142290745383015739287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21889854307732789271/10000000000000000000)
  centralHi := (218898543077327892711/100000000000000000000)
  directionLo := (110405178522389784587/50000000000000000000)
  directionHi := (8832414281791182767/4000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree059.table
  base := (-7730025692511794034283486150273177775543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-26129828141787400592639667930270000000000000)
      constant := (184715916807684346783222568810715757408869833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree059.table
  base := (-7730302945833752055634780923418374173543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-26870229272071355840767470871890000000000000)
      constant := (197123559990113251863030951242322472905207833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110405178522389784587/50000000000000000000)
  centralHi := (8832414281791182767/4000000000000000000)
  directionLo := (44541151936208068181/20000000000000000000)
  directionHi := (111352879840520170453/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree060.table
  base := (-3872328549462488964683705126283057785657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-1477452638593185479422287303885000000000000)
      constant := (10688836855592606077367459990759171516525263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree060.table
  base := (-3872452390899584268348640166095497268321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3080)
      previous := (1330)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-1519283210925612329598999334485000000000000)
      constant := (11402290777118560812503910933051885704670439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44541151936208068181/20000000000000000000)
  centralHi := (111352879840520170453/50000000000000000000)
  directionLo := (224585166500317987359/100000000000000000000)
  directionHi := (1403657290626987421/625000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree061.table
  base := (-3877930277753018334882571214779736290823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-13529233423783638333281337504795000000000000)
      constant := (100116081636508364987015741839649226661723513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree061.table
  base := (-387804089079201521011575287898362806253/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1984500000000000000000000000000000000000000
      center := (2772)
      previous := (1197)
      next := (0)
      square := (39529890854143373416992868917000000000000)
      linear := (-1391198316062534401239825258478500000000000)
      constant := (10675815932624923687765355728848898021981843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224585166500317987359/100000000000000000000)
  centralHi := (1403657290626987421/625000000000000000)
  directionLo := (226448975773443965361/100000000000000000000)
  directionHi := (113224487886721982681/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree062.table
  base := (-121306855842494816358728176820697469137/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-13761393100228607351762089274625000000000000)
      constant := (104107602831068311099641218673111855839847904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree062.table
  base := (-776383633440830661447486841581256336113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5544)
      previous := (2394)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-2830083484584035411681102231841000000000000)
      constant := (22194880450039233265694681947585993601967503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226448975773443965361/100000000000000000000)
  centralHi := (113224487886721982681/50000000000000000000)
  directionLo := (228297569513361379461/100000000000000000000)
  directionHi := (114148784756680689731/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree063.table
  base := (-7767994159050181551707768499706461700243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (890)
      previous := (370)
      next := (0)
      square := (12549171699728055053013609180000000000000)
      linear := (-444239770688050043499772731570000000000000)
      constant := (3434098111476837525094298376708492912884691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree063.table
  base := (-194204263884457385202008139258230392943/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (627458584986402752650680459000000000000)
      linear := (-22839447119388904927639317037500000000000)
      constant := (182967208838856169382798352466962970489182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228297569513361379461/100000000000000000000)
  centralHi := (114148784756680689731/50000000000000000000)
  directionLo := (115065657194679866799/50000000000000000000)
  directionHi := (230131314389359733599/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree064.table
  base := (-7768928845865411173044006335434659242903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-28451424906237090777447185628570000000000000)
      constant := (224631080882041820135141063832259837464917993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree064.table
  base := (-310763452765377393079078390794090869539/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11088)
      previous := (4788)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-5850914379003937260168011323218000000000000)
      constant := (47857189424349979505306379968035266693998545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115065657194679866799/50000000000000000000)
  centralHi := (230131314389359733599/100000000000000000000)
  directionLo := (7248455080507928537/3125000000000000000)
  directionHi := (46390112515250742637/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree065.table
  base := (-62131557853968134799050734053887531013/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11214)
      previous := (4662)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-5783148851825405762881737833646000000000000)
      constant := (46612779541687190371626694137183009735235075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree065.table
  base := (-3883292644635366052077375471848899550213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-14865720209804676196427286882465000000000000)
      constant := (124095294925980545130913758165906717685204603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/3125000000000000000)
  centralHi := (46390112515250742637/20000000000000000000)
  directionLo := (233755652544076137469/100000000000000000000)
  directionHi := (23375565254407613747/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree066.table
  base := (-7760543504849773969732849764184303238083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-3264451512446329650152243634210000000000000)
      constant := (26849624977991660970764291512924722272005397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree066.table
  base := (-1940167236016704243745315586377914542157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1540)
      previous := (665)
      next := (0)
      square := (21961050474524096342773816065000000000000)
      linear := (-839119692894417180135252525382500000000000)
      constant := (7145905707230569478014969861932339686908763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233755652544076137469/100000000000000000000)
  centralHi := (23375565254407613747/10000000000000000000)
  directionLo := (235546909793300213467/100000000000000000000)
  directionHi := (58886727448325053367/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree067.table
  base := (-1937806667251673724693552951295598766497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-14922191482453452444165848123775000000000000)
      constant := (125189628096903745845012621479370536991546814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree067.table
  base := (-7751338599002741986628760524415906703837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-30685177468788684576883608062610000000000000)
      constant := (266471988725627801806939369999963266292470947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235546909793300213467/100000000000000000000)
  centralHi := (58886727448325053367/25000000000000000000)
  directionLo := (11866232377005703071/5000000000000000000)
  directionHi := (237324647540114061421/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree068.table
  base := (-967311945697140001989343840535466571753/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-15154351158898421462646599893605000000000000)
      constant := (129630893280112194876841113171568932706849372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree068.table
  base := (-3869297713232714519270786582110632648267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-15581022996689175334449062605725000000000000)
      constant := (137924367497369649519067172332982899019028277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11866232377005703071/5000000000000000000)
  centralHi := (237324647540114061421/100000000000000000000)
  directionLo := (239089167355833222067/100000000000000000000)
  directionHi := (59772291838958305517/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree069.table
  base := (-7722351392649780347458147073540366290629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-3419224630076308995806078147430000000000000)
      constant := (29810467905106829942716696184268698465832611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree069.table
  base := (-1544488094600537271074509967101901190999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1232)
      previous := (532)
      next := (0)
      square := (17568840379619277074219052852000000000000)
      linear := (-703086989288178150242503163562000000000000)
      constant := (6341840891419705379077259535154061574769441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239089167355833222067/100000000000000000000)
  centralHi := (59772291838958305517/25000000000000000000)
  directionLo := (12042037988207382919/5000000000000000000)
  directionHi := (240840759764147658381/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree070.table
  base := (-1540559044381803059654154447044966798771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1134000000000000000000000000000000000000000
      center := (1602)
      previous := (666)
      next := (0)
      square := (22588509059510499095424496524000000000000)
      linear := (-892495457816477685691891624758000000000000)
      constant := (7927900734214388222411849511095503825096843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree070.table
  base := (-192571866860870375425272704706133431407/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283500000000000000000000000000000000000000
      center := (396)
      previous := (171)
      next := (0)
      square := (5647127264877624773856124131000000000000)
      linear := (-229398450303983448949479710779500000000000)
      constant := (2107673574062852542013471917108244688784462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12042037988207382919/5000000000000000000)
  centralHi := (240840759764147658381/100000000000000000000)
  directionLo := (242579704799552728083/100000000000000000000)
  directionHi := (60644926199888182021/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree071.table
  base := (-7679828013458788684379735552424216867123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-31701660376466657036177710406190000000000000)
      constant := (286808726404198112267764031050198283254388813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree071.table
  base := (-3839949434546998018133585456364777610767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-16296325783573674472470838328985000000000000)
      constant := (152461556216068357034258774023913197662865777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242579704799552728083/100000000000000000000)
  centralHi := (60644926199888182021/25000000000000000000)
  directionLo := (61076568132500906379/25000000000000000000)
  directionHi := (244306272530003625517/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree072.table
  base := (-7653450628855009011537156026753157851477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-3573997747706288341459912660650000000000000)
      constant := (32921201094058849119463111091841857387498643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree072.table
  base := (-765351380942705695477152186783801881637/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441000000000000000000000000000000000000000
      center := (616)
      previous := (266)
      next := (0)
      square := (8784420189809638537109526426000000000000)
      linear := (-367439112130411278188402153409000000000000)
      constant := (3499214147971526201173787981156343370198083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61076568132500906379/25000000000000000000)
  centralHi := (244306272530003625517/100000000000000000000)
  directionLo := (246020723546555450101/100000000000000000000)
  directionHi := (123010361773277725051/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree073.table
  base := (-3811831921283092706695326276024028406257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-16315149541123266555050358742755000000000000)
      constant := (152961386475316332227589619913920631255565967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree073.table
  base := (-7623720172167145751698159239429118362963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-33546388616326681128970710955650000000000000)
      constant := (325092780338747423663913786564215829217399853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246020723546555450101/100000000000000000000)
  centralHi := (123010361773277725051/50000000000000000000)
  directionLo := (247723309422502513317/100000000000000000000)
  directionHi := (123861654711251256659/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree074.table
  base := (-7590468352055009377970775969745277297243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-33094618435136471147062221025170000000000000)
      constant := (315704612948277756891804494764330994407242533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree074.table
  base := (-7590518567253678671872667153069164032347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-34023257140916347220985228104490000000000000)
      constant := (335413631075217367667623409433888487955614757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247723309422502513317/100000000000000000000)
  centralHi := (123861654711251256659/50000000000000000000)
  directionLo := (249414273144307404351/100000000000000000000)
  directionHi := (3897098017879803193/1562500000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree075.table
  base := (-118029137291398542722601322081828385657/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-1864385432668133843556873586935000000000000)
      constant := (18090907074536776937214776056156237821608416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree075.table
  base := (-1888477386414288488735479273455958276531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1540)
      previous := (665)
      next := (0)
      square := (21961050474524096342773816065000000000000)
      linear := (-958336824041833703138881812592500000000000)
      constant := (9608106203890146738989204277468422400049829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249414273144307404351/100000000000000000000)
  centralHi := (3897098017879803193/1562500000000000000)
  directionLo := (251093849516409782017/100000000000000000000)
  directionHi := (125546924758204891009/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree076.table
  base := (-7513853715351493443024822700025590798399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-34023257140916347220985228104490000000000000)
      constant := (335717913872417140840920504068018430121154369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree076.table
  base := (-7513893606245585615182631686215933610477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-34976994190095679405014262402170000000000000)
      constant := (356527355153224020849213308132408959500016787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251093849516409782017/100000000000000000000)
  centralHi := (125546924758204891009/50000000000000000000)
  directionLo := (252762265541824300477/100000000000000000000)
  directionHi := (126381132770912150239/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree077.table
  base := (-3735217826855898067408612057791713700413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (4005)
      previous := (1665)
      next := (0)
      square := (56471272648776247738561241310000000000000)
      linear := (-2463398320986163232710480831725000000000000)
      constant := (24710669321022999564890587060322098331865829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree077.table
  base := (-3735235600906011492741333070992465073459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (3960)
      previous := (1710)
      next := (0)
      square := (56471272648776247738561241310000000000000)
      linear := (-2532418765334667535502055682215000000000000)
      constant := (26237158908401283543014098180652272303348747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252762265541824300477/100000000000000000000)
  centralHi := (126381132770912150239/50000000000000000000)
  directionLo := (254419740780274279697/100000000000000000000)
  directionHi := (127209870390137139849/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree078.table
  base := (-7423611069885722190782758823197364250559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-3883543982966247032767581687090000000000000)
      constant := (39592299483252014341854307183999962365503481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree078.table
  base := (-7423642744367548359732639650335652275451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-3992303471030556843227032966650000000000000)
      constant := (42030047821995015915345742846341977346526109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254419740780274279697/100000000000000000000)
  centralHi := (127209870390137139849/50000000000000000000)
  directionLo := (256066487685460743423/100000000000000000000)
  directionHi := (1000259717521331029/390625000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree079.table
  base := (-28802267148313628692587415705640110323/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-17708107599793080665934869361735000000000000)
      constant := (183430943373042211272712072305457243472385664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree079.table
  base := (-7373408609790997712048869737925555438393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-36407599763864677681057813848690000000000000)
      constant := (389377970702372441775688577132943470465018183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256066487685460743423/100000000000000000000)
  centralHi := (1000259717521331029/390625000000000000)
  directionLo := (128851355961466775101/50000000000000000000)
  directionHi := (257702711922933550203/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree080.table
  base := (-731974400269649133180107170252034851411/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5607)
      previous := (2331)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-3588053455247609936883124226313000000000000)
      constant := (37754294314187374142391057818349673674749741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree080.table
  base := (-1829942285478794479463302807743424128767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-9221117072113585943268082749382500000000000)
      constant := (100160711066549363681594676817866349632923777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128851355961466775101/50000000000000000000)
  centralHi := (257702711922933550203/100000000000000000000)
  directionLo := (51865722533982204993/20000000000000000000)
  directionHi := (129664306334955512483/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree081.table
  base := (-7262702263595179921096294345592634459719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-4038317100596226378421416200310000000000000)
      constant := (43152651458395328199619287088073648203263921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree081.table
  base := (-290508986244773650809553318618779455853/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1232)
      previous := (532)
      next := (0)
      square := (17568840379619277074219052852000000000000)
      linear := (-830251929178755774779707736586000000000000)
      constant := (9157001107504220660864339753835591299844135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51865722533982204993/20000000000000000000)
  centralHi := (129664306334955512483/50000000000000000000)
  directionLo := (65236095724571356833/25000000000000000000)
  directionHi := (260944382898285427333/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree082.table
  base := (-1440451099726748773853799774883005800327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11214)
      previous := (4662)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-7361834651651195088550849868490000000000000)
      constant := (79870929080672910820585572173691349978502137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree082.table
  base := (-3601137721244468100395996166670814016839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-18919102668816837978550682647605000000000000)
      constant := (211822293132750360994136233248893539167166009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65236095724571356833/25000000000000000000)
  centralHi := (260944382898285427333/100000000000000000000)
  directionLo := (6563755241048814781/2500000000000000000)
  directionHi := (262550209641952591241/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree083.table
  base := (-892300500931572245418829790236888420769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-18636746305572956739857876441055000000000000)
      constant := (205242644393010407716622786161634159431871356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree083.table
  base := (-3569210884298009283500249809994294201649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-19157536931111671024557941222025000000000000)
      constant := (217690726243818170888070560487137646313655119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6563755241048814781/2500000000000000000)
  centralHi := (262550209641952591241/100000000000000000000)
  directionLo := (66036568562378524483/25000000000000000000)
  directionHi := (264146274249514097933/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree084.table
  base := (-707114806621111358181111457472549551781/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 63000000000000000000000000000000000000000
      center := (89)
      previous := (37)
      next := (0)
      square := (1254917169972805505301360918000000000000)
      linear := (-59901288831802938915360724479000000000000)
      constant := (669469511392777705787904250109229378237797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree084.table
  base := (-1414232776389407729406638675120408981713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (176)
      previous := (76)
      next := (0)
      square := (2509834339945611010602721836000000000000)
      linear := (-123149023450200025844858411406000000000000)
      constant := (1419922690545218056979203594115414234152081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66036568562378524483/25000000000000000000)
  centralHi := (264146274249514097933/100000000000000000000)
  directionLo := (265732752623318478719/100000000000000000000)
  directionHi := (415207425973935123/156250000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree085.table
  base := (-3500243965051441300837891129873075700491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-19101065658462894776819379980715000000000000)
      constant := (216598077282394421861208272045583762544751221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree085.table
  base := (-7000502012138891591730727897573320056217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-39268810911402674233144916741730000000000000)
      constant := (459327170456552683651509943107681492696874727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265732752623318478719/100000000000000000000)
  centralHi := (415207425973935123/156250000000000000)
  directionLo := (33413726930716670899/12500000000000000000)
  directionHi := (267309815445733367193/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree086.table
  base := (-1385284767115509998451192723293548583379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11214)
      previous := (4662)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-7733290133963145518120052700218000000000000)
      constant := (88955275001913752479631906784341905672568749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree086.table
  base := (-55411490982072208549052373431321603497/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11088)
      previous := (4788)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-7949135887198468065031886778114000000000000)
      constant := (94307204088866949024772694326897113893010175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33413726930716670899/12500000000000000000)
  centralHi := (267309815445733367193/100000000000000000000)
  directionLo := (268877628393472505833/100000000000000000000)
  directionHi := (134438814196736252917/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree087.table
  base := (-3424478001152499039034866233143198449199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-2173931667928092534864542613375000000000000)
      constant := (25361469591106663762644245114628849483903241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree087.table
  base := (-214030223845654801552079566191394875937/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1540)
      previous := (665)
      next := (0)
      square := (21961050474524096342773816065000000000000)
      linear := (-1117292998905055733810387528872500000000000)
      constant := (13441727685951463470458777497809258877694264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268877628393472505833/100000000000000000000)
  centralHi := (134438814196736252917/50000000000000000000)
  directionLo := (135218176170369706209/50000000000000000000)
  directionHi := (270436352340739412419/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree088.table
  base := (-3384042317456144279258969660470886901351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-19797544687797801832261635290205000000000000)
      constant := (234193193321838795912902601417451049888537881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree088.table
  base := (-6768094569442608671936206258700528040447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-40699416485171672509188468188250000000000000)
      constant := (496425698466493101705515692674977604207465857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135218176170369706209/50000000000000000000)
  centralHi := (270436352340739412419/100000000000000000000)
  directionLo := (271986143551892750981/100000000000000000000)
  directionHi := (135993071775946375491/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree089.table
  base := (-3341904962260296679599557672766429599451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-20029704364242770850742387060035000000000000)
      constant := (240208088131140881660042668021090040919778981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree089.table
  base := (-1336763753350320771046668280158698035641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11088)
      previous := (4788)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-8235257001952267720240597067418000000000000)
      constant := (101821305013417164109200979987744127496540871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271986143551892750981/100000000000000000000)
  centralHi := (135993071775946375491/50000000000000000000)
  directionLo := (273527153864286515913/100000000000000000000)
  directionHi := (136763576932143257957/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree090.table
  base := (-6596132050105907592291603503956116906249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-4502636453486164415382919739970000000000000)
      constant := (54732868976152970845577885384605352444344191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree090.table
  base := (-6596139919438449020684366474601772330261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-4628128170483444965913055831770000000000000)
      constant := (57993852871480751997548096761600618402354899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273527153864286515913/100000000000000000000)
  centralHi := (136763576932143257957/50000000000000000000)
  directionLo := (275059530861890566679/100000000000000000000)
  directionHi := (6876488271547264167/2500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree091.table
  base := (-6505051179704480771119436727588961949029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8010)
      previous := (3330)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-5855435347752202539343968742770000000000000)
      constant := (72132188506575234339681287626867058574900557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree091.table
  base := (-6505058182576194877626369290019434735159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7920)
      previous := (3420)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-6018574579848667255033145662110000000000000)
      constant := (76420021454247286533705814843508980505164847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275059530861890566679/100000000000000000000)
  centralHi := (6876488271547264167/2500000000000000000)
  directionLo := (138291709020126716633/50000000000000000000)
  directionHi := (276583418040253433267/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree092.table
  base := (-6410567471481376487468094503698265586487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-41452366787155355812369284739050000000000000)
      constant := (517404671916474334226992902737081583887233097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree092.table
  base := (-6410573702762683982717796833270619630371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-42606890583530336877246536783610000000000000)
      constant := (548092947494451696712651023000868910687057501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138291709020126716633/50000000000000000000)
  centralHi := (276583418040253433267/100000000000000000000)
  directionLo := (139049477481664640317/50000000000000000000)
  directionHi := (55619790992665856127/20000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree093.table
  base := (-3156340537339176364497922803996646903581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-2328704785558071880518377126595000000000000)
      constant := (29446326516909960094714275985427478715520779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree093.table
  base := (-6312686618919595580822722146076272804227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-4787084345346666996584561548050000000000000)
      constant := (62378118581789855109466480248970363693335893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139049477481664640317/50000000000000000000)
  centralHi := (55619790992665856127/20000000000000000000)
  directionLo := (139803138706327071811/50000000000000000000)
  directionHi := (279606277412654143623/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree094.table
  base := (-1242278426091061398749749702009152560181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11214)
      previous := (4662)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-8476201098587046377258458363674000000000000)
      constant := (108562587029895569928323280464835673488641611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree094.table
  base := (-6211397063000724293439361513897424079007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-43560627632709669061275571081290000000000000)
      constant := (574870508880977392700856181187161123830421217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139803138706327071811/50000000000000000000)
  centralHi := (279606277412654143623/100000000000000000000)
  directionLo := (281105517529322725239/100000000000000000000)
  directionHi := (7027637938233068131/2500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree095.table
  base := (-3053350386318909584251237421849457797607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-21422662422912584961626897679015000000000000)
      constant := (277870922460308155733329282890904502001297817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree095.table
  base := (-6106705160620403262905156446659509717839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-44037496157299335153290088230130000000000000)
      constant := (588495271930494498617687294487258405929897009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281105517529322725239/100000000000000000000)
  centralHi := (7027637938233068131/2500000000000000000)
  directionLo := (17662300246824120263/6250000000000000000)
  directionHi := (282596803949185924209/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree096.table
  base := (-2999303564190910858118788173569814480019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-2406091344373061553345294383205000000000000)
      constant := (31601144784061820624134091570095711814311621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree096.table
  base := (-5998611031611643093012185175716603285811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-4946040520209889027256067264330000000000000)
      constant := (66919706212115866072137878182308977950957349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17662300246824120263/6250000000000000000)
  centralHi := (282596803949185924209/100000000000000000000)
  directionLo := (142040130965830290927/50000000000000000000)
  directionHi := (56816052386332116371/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree097.table
  base := (-5887111318765105606021568541044413929137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-43773963551605045997176802437350000000000000)
      constant := (582049218246409476588652680662354721115255247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree097.table
  base := (-2943557395261192455844918370668688105589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-22495616603239333668659561263905000000000000)
      constant := (308108380180990751229382631773450976908917259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142040130965830290927/50000000000000000000)
  centralHi := (56816052386332116371/20000000000000000000)
  directionLo := (71389003370629124329/25000000000000000000)
  directionHi := (285556013482516497317/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree098.table
  base := (-5772213459314209306629432735600936453991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8010)
      previous := (3330)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-6319754700642140576305472282430000000000000)
      constant := (85061097265997370906686823166224269030587103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree098.table
  base := (-2886108273528619148989456629679567753081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (3960)
      previous := (1710)
      next := (0)
      square := (56471272648776247738561241310000000000000)
      linear := (-3247721552219166673523831405475000000000000)
      constant := (45022391775278073330503387900561685084003073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71389003370629124329/25000000000000000000)
  centralHi := (285556013482516497317/100000000000000000000)
  directionLo := (287024177470981358451/100000000000000000000)
  directionHi := (71756044367745339613/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree099.table
  base := (-226156546418968699987644899300892914647/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1246)
      previous := (518)
      next := (0)
      square := (17568840379619277074219052852000000000000)
      linear := (-993391161275220490468884655926000000000000)
      constant := (13532355411588279764610880158191531123203365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree099.table
  base := (-5653916406471174472894006840920138232389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-5104996695073111057927572980610000000000000)
      constant := (71618614329668931819764498748284219039516451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287024177470981358451/100000000000000000000)
  centralHi := (71756044367745339613/25000000000000000000)
  directionLo := (288484869741481697031/100000000000000000000)
  directionHi := (36060608717685212129/12500000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree100.table
  base := (-55322120280280988073997258424175221189/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5607)
      previous := (2331)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-4516692161027486010806131305633000000000000)
      constant := (62263415580502985330921384901494485471008590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree100.table
  base := (-345763404370053509784784797867973117687/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-11605459695061916403340668493582500000000000)
      constant := (164744723074968196843775611356298058783601188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288484869741481697031/100000000000000000000)
  centralHi := (36060608717685212129/12500000000000000000)
  directionLo := (7248455080507928537/2500000000000000000)
  directionHi := (289938203220317141481/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree101.table
  base := (-2703554331735711371540794135913755616671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-22815620481582399072511408297995000000000000)
      constant := (318231083654908736326794111367768303957432801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree101.table
  base := (-5407110834778593949178414298762521874437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-46898707304837331705377191123170000000000000)
      constant := (673547574465979528846472463010961550680359547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/2500000000000000000)
  centralHi := (289938203220317141481/100000000000000000000)
  directionLo := (145692144008772981989/50000000000000000000)
  directionHi := (291384288017545963979/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree102.table
  base := (-527860366434760209811591990123777472107/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441000000000000000000000000000000000000000
      center := (623)
      previous := (259)
      next := (0)
      square := (8784420189809638537109526426000000000000)
      linear := (-512172892400608179799825779285000000000000)
      constant := (7227111418318729356351429369694414134800813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree102.table
  base := (-5278605594913312856274538906160075731051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-5263952869936333088599078696890000000000000)
      constant := (76474841676974983049455740818763406602606509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145692144008772981989/50000000000000000000)
  centralHi := (291384288017545963979/100000000000000000000)
  directionLo := (292823231524342070353/100000000000000000000)
  directionHi := (146411615762171035177/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree103.table
  base := (-643337140568524564077713595801794606549/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-23279939834472337109472911837655000000000000)
      constant := (332283868224489380675851423555935708826428076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree103.table
  base := (-2573349420471190515085447206259333834513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-23926222177008331944703112710425000000000000)
      constant := (351578446910299204487204154039861704010817903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292823231524342070353/100000000000000000000)
  centralHi := (146411615762171035177/50000000000000000000)
  directionLo := (294255138506067042083/100000000000000000000)
  directionHi := (73563784626516760521/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree104.table
  base := (-5011389134582275894988259700927986146283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-47024199021834612255907327214970000000000000)
      constant := (678845293351466332027413683369216822985402773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree104.table
  base := (-5011390660457686654328378526698969703153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-48329312878606329981420742569690000000000000)
      constant := (718197530301798009234236082137051789248185743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294255138506067042083/100000000000000000000)
  centralHi := (73563784626516760521/25000000000000000000)
  directionLo := (147840055595642751097/50000000000000000000)
  directionHi := (59136022238257100439/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree105.table
  base := (-4872679781818369754304273227537076639657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (890)
      previous := (370)
      next := (0)
      square := (12549171699728055053013609180000000000000)
      linear := (-753786005948008734807441758010000000000000)
      constant := (11004328539831470801225207931265164171701609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree105.table
  base := (-4872681138228940032014920368056137238049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12549171699728055053013609180000000000000)
      linear := (-774701292114222159895797773310000000000000)
      constant := (11641198161903534413189120299462463354002913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147840055595642751097/50000000000000000000)
  centralHi := (59136022238257100439/20000000000000000000)
  directionLo := (297098249356937842747/100000000000000000000)
  directionHi := (74274562339234460687/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree106.table
  base := (-2365284575351056288430872761032334573057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-23976418863807244164915167147145000000000000)
      constant := (353924975043781511712466581595747664079536767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree106.table
  base := (-4730570356386819251213324468608448856457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-49283049927785662165449776867370000000000000)
      constant := (748750755188995724033240047079393066488722167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297098249356937842747/100000000000000000000)
  centralHi := (74274562339234460687/25000000000000000000)
  directionLo := (2332106643827118219/781250000000000000)
  directionHi := (298509650409871132033/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree107.table
  base := (-1146264330738082313577358073386829955017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-24208578540252213183395918916975000000000000)
      constant := (361288524630832702437847481262710343817075054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree107.table
  base := (-917011678917652613255167766772345094309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11088)
      previous := (4788)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-9951983690475065651492858803242000000000000)
      constant := (152852668590571757465037682888594562320687579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2332106643827118219/781250000000000000)
  centralHi := (298509650409871132033/100000000000000000000)
  directionLo := (299914409464916733127/100000000000000000000)
  directionHi := (37489301183114591641/12500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree108.table
  base := (-4436144377737982235229167504085384967471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-5431275159266040489305926819290000000000000)
      constant := (81939332801940910319005799852878345229345289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree108.table
  base := (-4436145330165938423517433571152785404009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-5581865219662777149942090129450000000000000)
      constant := (86659249687175389199648396066761621636832031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299914409464916733127/100000000000000000000)
  centralHi := (37489301183114591641/12500000000000000000)
  directionLo := (301312619419691738421/100000000000000000000)
  directionHi := (150656309709845869211/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree109.table
  base := (-4283830391838118235936134741212914975247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-49345795786284302440714844913270000000000000)
      constant := (752480787650235350993949907984025940463244657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree109.table
  base := (-4283831238263667600708226411168663535781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-50713655501554660441493328313890000000000000)
      constant := (795760467585909039827711900279941574426485211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301312619419691738421/100000000000000000000)
  centralHi := (150656309709845869211/50000000000000000000)
  directionLo := (75676092756572672327/25000000000000000000)
  directionHi := (302704371026290689309/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree110.table
  base := (-4128115439786702366411218798604058253663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-49810115139174240477676348452930000000000000)
      constant := (767657426264141571722873958703690492791211553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree110.table
  base := (-2064058095979693530569695700533121973303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-25595262013072163266753922731365000000000000)
      constant := (405872501933402034297507375843534038887960393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75676092756572672327/25000000000000000000)
  centralHi := (302704371026290689309/100000000000000000000)
  directionLo := (7602243824000603629/2500000000000000000)
  directionHi := (304089752960024145161/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree111.table
  base := (-1984499797002003661993963818224118049143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-2793024138448009917479880666255000000000000)
      constant := (43499106153986155151228203207828163940327937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree111.table
  base := (-793800052475404638368986621854842096611/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1232)
      previous := (532)
      next := (0)
      square := (17568840379619277074219052852000000000000)
      linear := (-1148164278905199836122719169146000000000000)
      constant := (18397485683221616117080136770892014635394549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7602243824000603629/2500000000000000000)
  centralHi := (304089752960024145161/100000000000000000000)
  directionLo := (152734425942675717189/50000000000000000000)
  directionHi := (305468851885351434379/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree112.table
  base := (-3806482924916031297163951076013089158419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8010)
      previous := (3330)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-7248393406422016650228479361750000000000000)
      constant := (114065748699077461025929096313580578447176427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree112.table
  base := (-3806483518788505907077014732233997459981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7920)
      previous := (3420)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-7449180153617665531076697108630000000000000)
      constant := (120598003277924960002688467651783323440190773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152734425942675717189/50000000000000000000)
  centralHi := (305468851885351434379/100000000000000000000)
  directionLo := (38355219064893288933/12500000000000000000)
  directionHi := (61368350503829262293/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree113.table
  base := (-1820282750531623627805967807007601399567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-25601536598922027294280429535955000000000000)
      constant := (407043208178739368942215637060346830045118577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree113.table
  base := (-3640566028706996853254252446536324578989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-52621129599913324809551396909250000000000000)
      constant := (860642505200350314271018620699207327745992659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38355219064893288933/12500000000000000000)
  centralHi := (61368350503829262293/20000000000000000000)
  directionLo := (308208537691426210417/100000000000000000000)
  directionHi := (154104268845713105209/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree114.table
  base := (-108476480912494862904231602933800231223/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-2870410697262999590306797922865000000000000)
      constant := (46103468716589610153849891487524105568490512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree114.table
  base := (-13884991431889128795249250101173371899/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441000000000000000000000000000000000000000
      center := (616)
      previous := (266)
      next := (0)
      square := (8784420189809638537109526426000000000000)
      linear := (-589977756938922121128510156201000000000000)
      constant := (9747292247203126630252033740692563574813525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308208537691426210417/100000000000000000000)
  centralHi := (154104268845713105209/50000000000000000000)
  directionLo := (77392322100917070801/25000000000000000000)
  directionHi := (61913857680733656641/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree115.table
  base := (-3298528654384419403653689247752284040627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-52131711903623930662483866151230000000000000)
      constant := (845788302258727287012096846275821184642751437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree115.table
  base := (-412316133853646072983340411184877260031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-13393716662273164248395107801732500000000000)
      constant := (223506853458570082454798497386476944309873922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77392322100917070801/25000000000000000000)
  centralHi := (61913857680733656641/20000000000000000000)
  directionLo := (155462041942414201501/50000000000000000000)
  directionHi := (310924083884828403003/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree116.table
  base := (-624481872012640795441781951863745343419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (11214)
      previous := (4662)
      next := (0)
      square := (158119563416573493667971475668000000000000)
      linear := (-10519206251302773739889073938178000000000000)
      constant := (172372802437200732316178363567176794731969989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree116.table
  base := (-390301216249952857310972197789529796279/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (13860)
      previous := (5985)
      next := (0)
      square := (197649454270716867084964344585000000000000)
      linear := (-13512933793420580771398737088942500000000000)
      constant := (227738959927350906783155621763796712477137298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155462041942414201501/50000000000000000000)
  centralHi := (310924083884828403003/100000000000000000000)
  directionLo := (62454600329034551793/20000000000000000000)
  directionHi := (156136500822586379483/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree117.table
  base := (-23543116545170559197875048982506893173/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1246)
      previous := (518)
      next := (0)
      square := (17568840379619277074219052852000000000000)
      linear := (-1179118902431195705253486071790000000000000)
      constant := (19513101476327128850193330240795861502767675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree117.table
  base := (-735722474187327526405395100250545760019/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1540)
      previous := (665)
      next := (0)
      square := (21961050474524096342773816065000000000000)
      linear := (-1514683436063110810489151819572500000000000)
      constant := (25778932767513551776354317734897009319831621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62454600329034551793/20000000000000000000)
  centralHi := (156136500822586379483/50000000000000000000)
  directionLo := (156808058764012769599/50000000000000000000)
  directionHi := (313616117528025539199/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree118.table
  base := (-1379984669539038307939134256920052608019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-26762334981146872386684188385105000000000000)
      constant := (447232482382487616429856203846819311198772589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree118.table
  base := (-2759969630949108679795927077744373768529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (55440)
      previous := (23940)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-55005472222861655269623982653450000000000000)
      constant := (945284633359905524078472024075692580512708399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156808058764012769599/50000000000000000000)
  centralHi := (313616117528025539199/100000000000000000000)
  directionLo := (157476752879765230327/50000000000000000000)
  directionHi := (62990701151906092131/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree119.table
  base := (-2573648731901754004597129941908553570139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8010)
      previous := (3330)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-7712712759311954687189982901410000000000000)
      constant := (130141458134632026792050125667087850125731187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree119.table
  base := (-2573648991132114328848826118564637846797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7920)
      previous := (3420)
      next := (0)
      square := (112942545297552495477122482620000000000000)
      linear := (-7926048678207331623091214257470000000000000)
      constant := (137526428666476964356943312593283850340866101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157476752879765230327/50000000000000000000)
  centralHi := (62990701151906092131/20000000000000000000)
  directionLo := (316285238996518530641/100000000000000000000)
  directionHi := (158142619498259265321/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree120.table
  base := (-595981951079871996482386590956347504579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-3025183814892978935960632436085000000000000)
      constant := (51536960707669326935887897163676501500961322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree120.table
  base := (-95357121381863471689186180016912547729/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1232)
      previous := (532)
      next := (0)
      square := (17568840379619277074219052852000000000000)
      linear := (-1243537983823133054525622598914000000000000)
      constant := (21783170695990426673406096743702707832257555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316285238996518530641/100000000000000000000)
  centralHi := (158142619498259265321/50000000000000000000)
  directionLo := (79402847093142347173/25000000000000000000)
  directionHi := (317611388372569388693/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree121.table
  base := (-2190806612747743675498834932303506003607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (56070)
      previous := (23310)
      next := (0)
      square := (790597817082867468339857378340000000000000)
      linear := (-54917628020963558884252887389190000000000000)
      constant := (944490221927929374720697269744207384671683817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree121.table
  base := (-1095403408602620305953939017843299234341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-28218038898315326772833767049985000000000000)
      constant := (498978837550141204737704355103654945338900571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79402847093142347173/25000000000000000000)
  centralHi := (317611388372569388693/100000000000000000000)
  directionLo := (79733005885587213907/25000000000000000000)
  directionHi := (318932023542348855629/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree122.table
  base := (-124642825773050890656032587321187787181/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-27690973686926748460607195464425000000000000)
      constant := (480732497146525067774111538181382645381428888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree122.table
  base := (-997142696965618198324941452249780989503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-28456473160610159818841025624405000000000000)
      constant := (507914990894942626779406235813030619252662593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79733005885587213907/25000000000000000000)
  centralHi := (318932023542348855629/100000000000000000000)
  directionLo := (320247212724300886929/100000000000000000000)
  directionHi := (32024721272430088693/10000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree123.table
  base := (-224295457147341851778752967990656624409/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3115)
      previous := (1295)
      next := (0)
      square := (43922100949048192685547632130000000000000)
      linear := (-3102570373707968608787549692695000000000000)
      constant := (54366089423283328000196245934279481714542524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree123.table
  base := (-1794363818401188698073188781667134293019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-6376646093978887303299618710850000000000000)
      constant := (114873289019481694377568411348174793776778621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320247212724300886929/100000000000000000000)
  centralHi := (32024721272430088693/10000000000000000000)
  directionLo := (321557022741767969481/100000000000000000000)
  directionHi := (160778511370883984741/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree124.table
  base := (-397760500007989339974959414489480039743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-28155293039816686497568699004085000000000000)
      constant := (497932033848149680062806276866032507444520066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree124.table
  base := (-795521071592735665270204034614332231723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-28933341685199825910855542773245000000000000)
      constant := (526023266523990291662056596553075715372291413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321557022741767969481/100000000000000000000)
  centralHi := (160778511370883984741/50000000000000000000)
  directionLo := (8071537976565252397/2500000000000000000)
  directionHi := (322861519062610095881/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree125.table
  base := (-692160146341547381711504797055382176823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-28387452716261655516049450773915000000000000)
      constant := (506644184159617222704974349864237188140189513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree125.table
  base := (-13843204197860698198778554085872960811/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1984500000000000000000000000000000000000000
      center := (2772)
      previous := (1197)
      next := (0)
      square := (39529890854143373416992868917000000000000)
      linear := (-2917177594749465895686280134766500000000000)
      constant := (53519538860170493739240015086603351092705705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8071537976565252397/2500000000000000000)
  centralHi := (322861519062610095881/100000000000000000000)
  directionLo := (162080382918694390603/50000000000000000000)
  directionHi := (324160765837388781207/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree126.table
  base := (-46967943433040319453060765488272897491/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (178)
      previous := (74)
      next := (0)
      square := (2509834339945611010602721836000000000000)
      linear := (-181711824715597616092255254246000000000000)
      constant := (3272579400910162621270604072489194037290335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree126.table
  base := (-146774837334025399054417452336565330467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3137292924932013763253402295000000000000)
      linear := (-233414366744361047641825872397500000000000)
      constant := (4321001323179804735970613638130592768361158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162080382918694390603/50000000000000000000)
  centralHi := (324160765837388781207/100000000000000000000)
  directionLo := (81363706484044784431/25000000000000000000)
  directionHi := (13018193037447165509/4000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree127.table
  base := (-9606769291304808201001731887429327957/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5607)
      previous := (2331)
      next := (0)
      square := (79059781708286746833985737834000000000000)
      linear := (-5770354413830318710602190862715000000000000)
      constant := (104858649640156032912806425945688929973386670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree127.table
  base := (-48033851465695653601280464772606693971/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1984500000000000000000000000000000000000000
      center := (2772)
      previous := (1197)
      next := (0)
      square := (39529890854143373416992868917000000000000)
      linear := (-2964864447208432504887731849650500000000000)
      constant := (55377560078266837207929169957976024031629101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81363706484044784431/25000000000000000000)
  centralHi := (13018193037447165509/4000000000000000000)
  directionLo := (408429701230087223/125000000000000000)
  directionHi := (326743760984069778401/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree128.table
  base := (-92969421409587511596203878209711524559/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (28035)
      previous := (11655)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-29083931745596562571491706083405000000000000)
      constant := (533230161735300047086493393963302619836101316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree128.table
  base := (-371877730106898324128714253502045611041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (27720)
      previous := (11970)
      next := (0)
      square := (395298908541433734169928689170000000000000)
      linear := (-29887078734379158094884577070925000000000000)
      constant := (563183690691490459310604702098730380969778271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell006.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408429701230087223/125000000000000000)
  centralHi := (326743760984069778401/100000000000000000000)
  directionLo := (328027631395407266801/100000000000000000000)
  directionHi := (164013815697703633401/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree129.table
  base := (-523433959987735881435656570526377724167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6230)
      previous := (2590)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-6514686982675895908882768411830000000000000)
      constant := (120498221367156406188777215137197867423642353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree129.table
  base := (-523434038937041173599071341332655692107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6160)
      previous := (2660)
      next := (0)
      square := (87844201898096385371095264260000000000000)
      linear := (-6694558443705331364642630143410000000000000)
      constant := (127260096967273009849714008007502298839780813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell006.Kernel129
